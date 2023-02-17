
import unicode
import strformat
import tables
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
    if node.argind >= depth: nArg(node.argind + 1)
    else: nArg(node.argind)
  of nkFunc:
    nFunc(node.body.dobble(depth+1))
  of nkExpr:
    nExpr(node.sexpr.dobble(depth))

func dedobblenode(node: Node, depth=0): Node
func dedobble(exp: Expression, depth=0): Expression =
  case exp.kind
  of ekTermin: exp
  of ekLink: link(dedobbleNode(exp.held, depth), dedobble(exp.next, depth))

func dedobblenode(node: Node, depth=0): Node =
  case node.kind
  of nkArg:
    if node.argind >= depth: nArg(node.argind - 1)
    else: node
  of nkFunc:
    nFunc(node.body.dedobble(depth + 1))
  of nkExpr:
    nExpr(node.sexpr.dedobble(depth))

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

func renderShape(self: Expression | Node): string =
  when self is Expression:
    case self.kind
    of ekLink:
      result = fmt"("
      var nodes = newSeq[Node]()
      var acc = self
      while acc.kind != ekTermin:
        nodes.add (acc.held)
        acc = acc.next
      let ei = nodes.len - 1
      for i, node in nodes:
        result &= node.renderShape()
        if i != ei: result &= ", "
      result.add ')'
      return
    of ekTermin:
      $self.kind
  else:
    case self.kind
    of nkArg:
      $self.kind
    of nkFunc:
      fmt"{self.kind}[{self.body.renderShape}]"
    of nkExpr:
      fmt"{self.kind}[{self.sexpr.renderShape}]"



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
    if node.argind == depth:
      value
    else: node
  of nkFunc:
    nFunc(node.body.subst(value, depth + 1))
  of nkExpr:
    nExpr(node.sexpr.subst(value, depth))

type Action = enum
  Nothing
  ErrorEmptyExpression
  ErrorFunction
  Unpacking
  BetaReduction
  EttaReduction

const TerminalActions = {Nothing, ErrorEmptyExpression, ErrorFunction}

func waddle(exp: Expression): tuple[res: Expression, act: Action]
func step(exp: Expression): tuple[res: Expression, act: Action] =
  case exp.kind
  of ekLink:
    if exp.next.kind == ekTermin:
      if exp.held.kind == nkExpr:
        (exp.held.sexpr, Unpacking)
      else:
        waddle(exp)
    elif exp.held.kind == nkFunc:
      let fres = exp.held.body.subst(exp.next.held)#exp.next.held.dobbleNode).dedobble
      (link(nExpr(fres), exp.next.next), BetaReduction)
    else:
      waddle(exp)
  of ekTermin:
    waddle(exp)

func waddle(exp: Expression): tuple[res: Expression, act: Action] =
  case exp.kind
  of ekTermin:
    (exp, Nothing)
  of ekLink:
    let (held, next) = (exp.held, exp.next)
    case held.kind
    of nkExpr:
      if held.sexpr.kind == ekTermin:
        (exp, ErrorEmptyExpression)
      elif held.sexpr.next.kind == ekTermin:
        (link(held.sexpr.held, next), Unpacking)
      else:
        let (nsexpr, act) = step(held.sexpr)
        if act == Nothing:
          let (nnext, nact) = waddle(next)
          (link(exp.held, nnext), nact)
        else:
          (link(nExpr(nsexpr), next), act)
    of nkFunc:
      let (nfbod, act) = step(held.body)
      (link(nFunc(nfbod), next), act)
    of nkArg:
      let (res, act) = waddle(next)
      (exp.held.link res, act)

func accumNodes(xs: sink seq[Node]): Expression =
  result = termin()
  while xs.len > 0:
    result = link(xs.pop(), result)

type ParseResult[T] = object
  case isError: bool
  of true:
    error: string
  of false:
    value: T

func qParse(input: string, env: TableRef[char, Expression]): ParseResult[Expression] =
  type ParseContext = enum
    BaseExpression, Function, SubExpression
  type ContextFrame = object
    context: ParseContext
    start: int
    exprs: seq[Node]

  var ind = 0
  var contextStack = newSeq[ContextFrame]()
  template cur: ContextFrame = contextStack[^1]
  template atEnd: bool = ind == input.len
  template pushContext(cont: ParseContext) =
    contextStack.add ContextFrame(context: cont, start: ind, exprs: newSeq[Node]())
  template popContext: ContextFrame = contextStack.pop()
  template get: char = input[ind]
  template step      = ind += 1
  pushContext(BaseExpression)

  while not atEnd:
    case get()
    of ' ':
      step(); continue
    of ')':
      step()
      while cur.context != SubExpression:
        let prev = popContext
        if prev.context == BaseExpression:
          return ParseResult[Expression](isError: true, error: "Mismatch parenthesis [closing]")
        cur.exprs.add nFunc(accumNodes(prev.exprs))
      let sexpr = nExpr(accumNodes(popContext.exprs))
      cur.exprs.add sexpr
    of '(':
      step()
      pushContext(SubExpression)
    of '/':
      step()
      pushContext(Function)
    of '0' .. '9':
      cur.exprs.add nArg(get().int - '0'.int)
      step()
    else:
      if get() in env:
        cur.exprs.add nExpr(env[get()])
        step()
      else:
        return ParseResult[Expression](isError: true, error: fmt"Unrecognised name {get().repr}")
  
  while cur.context != BaseExpression:
    let prev = popContext
    if prev.context == SubExpression:
      return ParseResult[Expression](isError: true, error: "Mismatch parenthesis [cleanup]")
    cur.exprs.add nFunc(accumNodes(prev.exprs))
  
  return ParseResult[Expression](isError: false, value: accumNodes(cur.exprs))

let env = (block:
  var tmp = newTable[char, Expression]()
  tmp['+'] = qParse("////31(210)", tmp).value
  tmp['z']= qParse("//0", tmp).value
  tmp[',']= qParse("///021", tmp).value
  tmp['>']= qParse("//0", tmp).value
  tmp['<']= qParse("//1", tmp).value
  tmp['.']= qParse("///1(210)", tmp).value
  tmp['f']= qParse("/0(/,(0>)(+(0<)(0>)))(,z(.z))<",tmp).value
  tmp['I']= qParse("/0",tmp).value
  tmp['K']= qParse("//1",tmp).value
  tmp['S']= qParse("///2 0 (1 0)",tmp).value
  tmp['*']= qParse("////3(21)",tmp).value
  tmp
)
when not defined(timing):
  let RV = qParse(stdin.readLine(), env) #"/ (/ 0 0) (//2)")
else:
  let RV = qParse("f (.(.(.(.(.(.z))))))", env)
if RV.isError:
  echo(RV.error)
else:
  let V = RV.value
  var (res, act) = V.step()
  while act notin TerminalActions:
    #echo res.renderShape()
    when not defined(timing): echo act, ": ", res.render()
    (res, act) = res.step()
  #echo res.renderShape()
  when not defined(timing): echo act, ": ", res.render()
