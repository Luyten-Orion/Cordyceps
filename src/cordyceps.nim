import std/[strutils, macros]

import pkg/micros

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
        res[0][0][0] = res[0][0].copyNimTree()

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

  result = body

  # Create a statement list and add an object spore (the internal implementation type)
  var typeSec = newNimNode(nnkTypeSection)
  var sporeBody = newStmtList(newNimNode(nnkTypeSection)).stmtList
  sporeBody[0].add stripEmptyPragmaExpr(body.copyNimTree.objectDef)

  var objSpore = sporeBody[0][0].objectDef
  if objSpore.NimNode[^1].kind == nnkRefTy:
    objSpore.NimNode[^1] = objSpore.NimNode[^1][0]

  # Set the name and unmark it as exported if required
  objSpore.exported = false
  objSpore.name = $objSpore.name & "Spore"

  # Create distinct types for the spore and also make sure no conditional fields are defined yet,
  # since that's our job
  for field in objSpore.fields:
    let cond = fieldConditions(objSpore.NimNode, field.name)
    if cond.kind != nnkSym and cond.strVal != "true":
      error("Spores can't have conditional fields in the definition!", cond)
      return

    typeSec.insert 0, newNimNode(nnkTypeDef)
    var tp = typeSec[0]
    tp.add field.name.NimNode
    tp.add objSpore.genericParamList
    tp.add newNimNode(nnkDistinctTy)
    tp[2].add body.objectDef.accessObj


  # Create the enum's name and define the variables needed
  var
    enumName = nimName(($objSpore.name)[0..<(^5)] & "Kind")
    enumFields = newSeq[NimNode]()
    enumPrefix = ""

  for c in $($objSpore.name)[0..<(^5)]:
    if c.isUpperAscii:
      enumPrefix.add c.toLowerAscii

  enumName.NimNode.copyLineInfo(objSpore.name.NimNode)

  # Iterate over the fields in the spore and define the fields
  for i in objSpore.fields:
    var field = enumField($enumPrefix & $i.name, none(int))
    #field.NimNode.copyLineInfo(i.NimNode)
    enumFields.add field.NimNode

    #[
    var initProc = routineNode(nimName("init"), rtProc)
    initProc.addGeneric identDef(nimName("T"), i.name.NimNode)
    initProc.addParam identDef(nimName("_"), nimName("T").NimNode)
    initProc.returnType = nimName("T").NimNode

    var initCall = newNimNode(nnkCall)
    initCall.add i.name.NimNode
    initCall.add newNimNode(nnkObjConstr)
    initCall[^1].add body.objectDef.accessObj
    initCall[^1].add newNimNode(nnkExprColonExpr)
    initCall[^1][^1].add ident("kind")
    initCall[^1][^1].add field.name.NimNode

    # Add to bodies
    initProc.addToBody initCall
    sporeBody.add initProc
    ]#

  # Create the enum and add it to the list
  var enumSpore = enumDef(enumName, enumFields, body.objectDef.exported)

  # Add the enum to the statement list
  typeSec.add enumSpore.NimNode[0]

  # Make the case statement and conditional fields
  var recCase = newNimNode(nnkRecCase)

  recCase.add identDef(exported("kind"), enumName.NimNode)

  for i in objSpore.fields:
    recCase.add newNimNode(nnkOfBranch)
    let enumCase = nimName(enumPrefix & $i.name)
    recCase[^1].add enumCase.NimNode
    recCase[^1].add newNimNode(nnkRecList)
    var field = identDef(exported($i.name & "Data"), i.typ)
    field.name.NimNode.copyLineInfo(i.name.NimNode)
    recCase[^1][^1].add field.NimNode

  # Edit the spore body
  objSpore.recList = newNimNode(nnkRecList, objSpore.recList)
  objSpore.recList.add recCase

  # Add the return type to the statement list
  if body[^1].kind == nnkRefTy:
    sporeBody.add newNimNode(nnkRefTy)
    sporeBody.NimNode[^1].add objSpore.accessObj
  else:
    sporeBody.add objSpore.accessObj

  # Set the body of the returned type to the statement list
  result[^1] = sporeBody.NimNode

  typeSec.add result
  result = typeSec

  echo result.repr
  echo result.treeRepr

type
  MOption*[T] {.spore.} = ref object
    None: void
    Some: T

Some[int].init()