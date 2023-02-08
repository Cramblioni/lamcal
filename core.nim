
# new core for lamcal

type NID = distinct uint32
proc getNID: NID =
  var c {. global .} = 0
  inc c
  NID(c)

type
  
  NodeKind = enum
    nkFuncDef, nkReference

  NodeObj = object
    case kind: NodeKind
    of nkFuncDef:
      arg: NID
      body: Node
    of nkReference:
      refs: NID

  Node = ref NodeObj

