import std/[macros, strutils, typetraits, tables]

import pkg/micros

type
  CordycepsUnpackDefect* = object of Defect

# Couldn't figure out a good way to represent this using
# a cache table
var Stipes {.compileTime.}: Table[string, Table[string,
  tuple[value, field: NimNode]]]

proc `[]`(stmtList: StmtList, index: int): NimNode = stmtList.NimNode[index]
proc `[]=`(stmtList: StmtList, index: int, value: StmtSubTypes) = stmtList.NimNode[index] = value.NimNode
proc len(stmtList: StmtList): int = stmtList.NimNode.len

proc stripEmptyPragmaExpr(typeDef: TypeDefs): TypeDefs =
  result = typeDef
  var res = result.NimNode

  # Copy the pragmas still on the tree if any remain
  case res[0].kind
    of nnkPragmaExpr:
      # If no unused pragmas are left:
      if res[0][1].len == 0:
        # Remove the empty pragma section
        res[0] = res[0][0].copyNimTree()

    else:
      discard

proc exported(typeDef: TypeDefs): bool =
  let obj = typeDef.NimNode

  case obj[0].kind
    # Check for a postfix
    of nnkPostfix:
     return true
    # Check for a pragma expression
    of nnkPragmaExpr:
      case obj[0][0].kind
        of nnkPostfix:
          return true
        of nnkIdent:
          return false
        else:
          error("Unexpected node kind `" & $obj[0][0].kind & "`!", obj[0][0])
    # Check for an ident
    of nnkIdent:
      return false
    # Unhandled node kinds should create an error. Could be changed to a warning with default value of false?
    else:
      error("Unexpected node kind `" & $obj[0].kind & "`!", obj[0])

proc `exported=`(typeDef: TypeDefs, value: bool) =
  let obj = typeDef.NimNode
  var target: NimNode

  case obj[0].kind
    # Check for a postfix
    of nnkPostfix:
      if not value:
        target = obj[0]
      else:
        return
    # Check for a pragma expression
    of nnkPragmaExpr:
      case obj[0][0].kind
        of nnkPostfix:
          if not value:
            target = obj[0][0]
          else:
            return
        of nnkIdent:
          if value:
            target = obj[0][0]
          else:
            return
        else:
          error("Unexpected node kind `" & $obj[0][0].kind & "`!", obj[0][0])
    # Check for an ident
    of nnkIdent:
      if value:
        target = obj[0]
      else:
        return
    # Unhandled node kinds should create an error. Could be changed to a warning with default value of false?
    else:
      error("Unexpected node kind `" & $obj[0].kind & "`!", obj[0])

  if value:
    var postfix = newNimNode(nnkPostfix)
    postfix.add ident("*")
    postfix.add target.copy()
    target[] = postfix[]
  else:
    target[] = target[1][]

proc accessObj(objDef: ObjectDef): NimNode =
  if objDef.genericParamList.len > 0:
    # Create a bracket expr
    result = newNimNode(nnkBracketExpr)
    result.add objDef.name.NimNode

    # Add the generic parameters
    for i in objDef.genericParams:
      if i.isSingle:
        result.add i.name.NimNode
      else:
        for n in i.names:
          result.add n.NimNode

  else:
    # Return the name
    result = objDef.name.NimNode

macro spore*(body): ObjectDef =
  ## Creates a sum type that's defined via a pragma.
  if not body.isa ObjectDef:
    error("`spore` can only be used on type definitions!", body)

  if body.objectDef.inheritObj.isSome:
    error("`spore` can't be used in conjunction with inheritance!", body)

  var hasOneField = false
  for i in body.objectDef.fields:
    hasOneField = true
    break
  if not hasOneField:
    error("`spore` requires at least one field to be defined!", body)

  result = body.copyNimTree

  # Create a statement list and add an object spore (the internal implementation type)
  var typeSec = newNimNode(nnkTypeSection)
  var sporeBody = newStmtList(newNimNode(nnkTypeSection)).stmtList
  sporeBody[0].add stripEmptyPragmaExpr(body.copyNimTree.objectDef)

  var objSpore = sporeBody[0][0].objectDef
  if objSpore.NimNode[^1].kind == nnkRefTy:
    objSpore.NimNode[^1] = objSpore.NimNode[^1][0]

  # Create distinct types for the spore and also make sure no conditional fields are defined yet,
  # since that's our job
  for field in objSpore.fields:
    let cond = fieldConditions(objSpore.NimNode, field.name)
    if cond.kind != nnkSym and cond.strVal != "true":
      error("Spores can't have conditional fields in the definition!", cond)
      return

    typeSec.insert 0, newNimNode(nnkTypeDef)
    var tp = typeSec[0]
    tp.add if not body.objectDef.exported:
        field.name.NimNode
      else:
        exported($field.name).NimNode
    tp.add objSpore.genericParamList
    tp.add newNimNode(nnkDistinctTy)
    tp[2].add body.objectDef.accessObj

  # Create the enum's name and define the variables needed
  var
    enumName = nimName($objSpore.name & "Kind")
    enumFields = newSeq[NimNode]()
    enumPrefix = ""

  for c in $objSpore.name:
    if c.isUpperAscii:
      enumPrefix.add c.toLowerAscii

  enumName.NimNode.copyLineInfo(objSpore.name.NimNode)

  # Create a table used for lookup
  Stipes[$objSpore.name] = initTable[string, (NimNode, NimNode)]()

  # Create template for code reuse
  template eField(nm: NimName) =
    var field = enumField($enumPrefix & $nm, none(int))
    #field.NimNode.copyLineInfo(i.NimNode)
    enumFields.add field.NimNode

    Stipes[$objSpore.name][$nm] = (
      ident($field.name), ident($nm & "Data")
    )

  # Iterate over the fields in the spore and define the fields
  for i in objSpore.fields:
    if i.isSingle:
      eField(i.name)
    else:
      for nm in i.names:
        eField(nm)

  # Create the enum and add it to the list
  var enumSpore = enumDef(enumName, enumFields, body.objectDef.exported)

  # Add the enum to the statement list
  typeSec.add enumSpore.NimNode[0]

  # Make the case statement and conditional fields
  var recCase = newNimNode(nnkRecCase)

  recCase.add identDef(exported("kind"), enumName.NimNode)

  template cStmt(i: IdentDef, nm: NimName) =
    recCase.add newNimNode(nnkOfBranch)
    let enumCase = nimName(enumPrefix & $nm)
    recCase[^1].add enumCase.NimNode
    recCase[^1].add newNimNode(nnkRecList)
    var field = identDef(exported($nm & "Data"), i.typ)
    field.name.NimNode.copyLineInfo(nm.NimNode)
    recCase[^1][^1].add field.NimNode

  for i in objSpore.fields:
    if i.isSingle:
      cStmt(i, i.name)
    else:
      for nm in i.names:
        cStmt(i, nm)
  # Clear the fields
  objSpore.recList = newNimNode(nnkRecList, objSpore.recList)

  # Edit the spore body
  objSpore.recList.add recCase

  # Set the body of the returned type to the statement list
  typeSec.add objSpore.NimNode

  #typeSec.add result
  result = typeSec

proc resolveUnderlyingType(typ: NimNode): NimNode =
  if typ.getImpl[^1].kind == nnkDistinctTy:
    typ.getImpl[^1][^1]
  else:
    typ.getImpl[^1]

macro unpack*(target: typed) =
  var typ = target.getTypeInst
  var lastTypSym: NimNode
  template typSym: NimNode = (if typ.kind in {nnkSym, nnkEmpty}: typ else: typ[0])
  var base: NimNode = typSym

  while true:
    lastTypSym = typSym
    if base.kind == nnkSym and base.strVal notin Stipes:
      typ = resolveUnderlyingType(typSym)
      while base.kind != nnkSym or base.strVal notin Stipes:
        base = typSym.getImpl[^1][0]
        if base.kind notin {nnkSym, nnkEmpty}:
          lastTypSym = typSym
          base = base[0]
        else:
          break
        continue
    break

  if base.kind == nnkEmpty:
    typ = target.getTypeInst
    base = typSym.getImpl
    base = (if base.kind in {nnkSym, nnkEmpty}: base else: base[^1][0])
    base = (if base.kind in {nnkSym, nnkEmpty}: base else: base[0])

  if base.strVal != lastTypSym.strVal:
    if lastTypSym.strVal notin Stipes[base.strVal]:
      error("`" & target.strVal & "` isn't a valid distinct sum type of `" & base.strVal & "`!", target)

  else:
    error("You must use a distinct sum type!", target)

  var ifRes = ifStmt()

  let elifCond = infix(
    newDotExpr(newCall(typ.getTypeImpl[0], target),
      ident("kind")),
      "==", newDotExpr(ident(base.strVal & "Kind"),
      Stipes[base.strVal][typSym.strVal].value
    )
  )
  let elifBody = newDotExpr(newCall(typ.getTypeImpl[0], target),
    Stipes[base.strVal][typSym.strVal].field)

  var elifRes = elifBranch(elifCond, elifBody)

  var elseRes = newNimNode(nnkElse)
  elseRes.add quote do:
    raise newException(typedesc[`CordycepsUnpackDefect`],
      "Couldn't unpack the given object because of the discrepancy between the type and the internal object kind!")

  ifRes.add elifRes
  ifRes.add elseRes.elseBranch
  result = ifRes.NimNode

macro dispatchIt*(target: typed, body: untyped): untyped =
  var typ = target.getTypeInst
  template typSym: NimNode = (if typ.kind == nnkSym: typ else: typ[0])

  while typ.kind != nnkEmpty and typSym.strVal notin Stipes:
    typ = resolveUnderlyingType(typSym)

  if typSym.strVal notin Stipes:
    error("Can't unpack the target as it only operates on unknowns!", target)

  result = newNimNode(nnkStmtList)

  let tmp = genSym(nskLet, ":tmp")

  result.add quote do:
    let `tmp` = `target`

  let res = caseStmt(nimName("_"))
  res.discriminator[] = newDotExpr(tmp, ident("kind"))[]

  for field in Stipes[typSym.strVal].keys:
    let tup = Stipes[typSym.strVal][field]
    var bod = typ.copyNimTree()
    if typ.kind != nnkSym:
      bod[0] = ident(field)
    else:
      bod = ident(field)

    var stmt = stmtList(newNimNode(nnkStmtList))
    #stmt.add newLetStmt(ident("it"), newCall(bod, target))
    let it = ident("it")
    stmt.add quote do:
      template `it`: auto {.used.} = `bod`(`tmp`)
    stmt.add body.copyNimTree()

    res.add ofBranch(tup.value, stmt.NimNode)

  result.add res.NimNode
