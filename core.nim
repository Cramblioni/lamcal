
import unicode
# new core using debruijn indexing to simplify
# all of this

type
  ExpressionKind = enum
    ekLink, ekTermin
  Expression = ref object
    case kind: ExpressionKind
    of ekLink:
      held: Node
      next: Expression
    of ekTermin:
      discard

  NodeKind = enum
    nkArg, nkFunc, nkExpr
  Node = object
    case kind: NodeKind
    of nkArg:
      argind: int
    of nkFunc:
      body: Expression
    of nkExpr:
      sexpr: Expression

func termin: Expression =
  Expression(kind: ekTermin)
func link(held: Node, next: Expression): Expression =
  Expression(kind: ekLink, held: held, next: next)

func nArg(ind: int): Node = Node(kind: nkArg, argind: ind)
func nFunc(body: Expression): Node = Node(kind: nkFunc, body: body)
func nExpr(sexpr: Expression): Node = Node(kind: nkExpr, sexpr: sexpr)

func dobbleNode(node: Node, depth=0): Node
func dobble(exp: Expression, depth=0): Expression =
  ## takes a function body, if an arguments index exceeds the function body, it gets incremented
  # deep recursion here i come
  case exp.kind
  of ekLink:
    link(exp.held.dobbleNode(depth), exp.next.dobble(depth))
  of ekTermin:
    termin()

func dobbleNode(node: Node, depth=0): Node =
  case node.kind
  of nkArg:
    if node.argind > depth: nArg(node.argind + 1)
    else: nArg(node.argind)
  of nkFunc:
    nFunc(node.body.dobble(depth+1))
  of nkExpr:
    nExpr(node.sexpr.dobble(depth))

func render(node: Node, eoe=false): string
func render(exp: Expression): string =
  # deconstruct, reconstruct
  var nodes = newSeq[Node]()
  var acc = exp
  while acc.kind != ekTermin:
    nodes.add acc.held
    acc = acc.next
  let ei = nodes.len - 1
  for i, node in nodes:
    result &= node.render(i >= ei)
    if i < ei: result.add ' '

func render(node: Node, eoe=false): string =
  case node.kind
  of nkArg:
    $node.argind
  of nkFunc:
    if eoe: "λ" & node.body.render()
    else: "(λ" & node.body.render() & ")"
  of nkExpr:
    "(" & node.sexpr.render() & ")"

func substNode(node: Node, value: Node, depth=0): Node
func subst(fbod: Expression, value: Node, depth=0): Expression =
  case fbod.kind
  of ekLink:
    link(fbod.held.substNode(value, depth), fbod.next.subst(value, depth))
  of ekTermin:
    termin()

func substNode(node: Node, value: Node, depth=0): Node =
  case node.kind
  of nkArg:
    if node.argind == depth: value
    else: node
  of nkFunc:
    nFunc(node.body.subst(dobbleNode(value, depth), depth + 1))
  of nkExpr:
    nExpr(node.sexpr.subst(value, depth))

let e = link(nFunc(link(nFunc(link(nArg(1), termin())), termin())), termin())
echo e.render
echo e.held.body.subst(nArg(1336)).render


