import unicode, streams, tables
import strformat

const LAMBDA = "λ".runeAt(0)

type
  Elemkind = enum
    ekFunc, ekIdent
  Elem = ref object
    case kind: Elemkind
    of ekFunc:
      arg:  seq[Rune]
      body: Node
    of ekIdent:
      id: seq[Rune]
  NodeKind = enum
    nkElem, nkLink, nkTermin
  Node = ref object
    case kind: NodeKind
    of nkElem:
      elem: Elem
    of nkLink:
      held: Node
      next: Node
    of nkTermin:
      discard

func render(exp: Node): string =
  var buff = newSeq[Node]()
  var cur = exp
  while cur.kind == nkLink:
    buff.add cur.held
    cur = cur.next
  if cur.kind != nkTermin: buff.add cur

  let ei = buff.len - 1
  for i, e in buff:
    case e.kind
    of nkElem:
      case e.elem.kind
      of ekIdent:
        result.add $e.elem.id
      of ekFunc:
        if buff.len != 1: result.add '('
        result &= $LAMBDA & $e.elem.arg
        result.add '.'
        result &= e.elem.body.render
        if buff.len != 1: result.add ')'
    of nkLink:
      result.add '('
      result &= e.render
      result.add ')'
    of nkTermin: discard
    if i != ei: result.add ' '

func subst(e: Node, i: seq[Rune], v: Node): Node =
  case e.kind
  of nkElem:
    case e.elem.kind
    of ekFunc:
      if e.elem.arg != i:
        Node(kind: nkElem,
          elem: Elem(kind: ekFunc, arg: e.elem.arg,
                     body: e.elem.body.subst(i, v)))
      else:
        e
    of ekIdent:
      if e.elem.id == i:
        v
      else: e
  of nkLink:
    Node(kind: nkLink,
      held: e.held.subst(i, v),
      next: e.next.subst(i, v))
  of nkTermin: e

func apply(f, x: Node): Node =
  ## ::= f x
  assert f.kind == nkElem
  let ef = f.elem
  ef.body.subst(ef.arg, x)

type Action = enum
  None, Apply, Unpack, Subbing

type Env = Table[seq[Rune], Node]
func modifMid(exp: Node, env: Env): tuple[res: Node, act: Action]

func modif(exp: Node, env: Env): tuple[res: Node, act: Action] =
  case exp.kind
  of nkTermin:
    return (exp, None)
  of nkElem:
    if exp.elem.kind == ekFunc:
      let (nbody, act) = exp.elem.body.modif(env)
      let nfunc = Elem(kind: ekFunc, arg: exp.elem.arg, body: nbody)
      return (Node(kind: nkElem, elem: nfunc), act)
    return (exp, None)
  of nkLink:
    let (held, next) = (exp.held, exp.next)
    if next.kind == nkTermin and held.kind != nkLink:
      return (held, Unpack)
    if held.kind == nkLink:
      let (res, act) = modif(held, env)
      if act != None:
        return (Node(kind: nkLink, held: res, next: next), act)
    if held.kind == nkElem and next.kind == nkLink:
      if held.elem.kind == ekFunc:
        return (Node(kind: nkLink, held: held.apply(next.held),
                                   next: next.next), Apply)
      if held.elem.id in env:
        return (exp.subst(held.elem.id, env[held.elem.id]), Subbing)
    return modifMid(exp, env)

func modifMid(exp: Node, env: Env): tuple[res: Node, act: Action] =
  if exp.kind != nkLink: return (exp, None)
  let (held, next) = (exp.held, exp.next)
  if held.kind == nkLink:
    let (nheld, act) = modif(held, env)
    if act != None:
      return (Node(kind: nkLink, held: nheld, next: next), act)
  let (nnext, act) = modifMid(next, env)
  return (Node(kind: nkLink, held: held, next: nnext), act)

proc readRune(stream: Stream): Rune =
  let l = stream.peekStr(1).runeLenAt(0)
  stream.readStr(l).runeAt(0)

proc peekRune(stream: Stream): Rune =
  let l = stream.peekStr(1).runeLenAt(0)
  stream.peekStr(l).runeAt(0)

proc skip(stream: Stream) =
  while (not stream.atEnd()) and stream.peekRune in " \t".toRunes:
    discard stream.readRune()

proc parseExpression(stream: Stream): Node

proc parseIdentImpl(stream: Stream): seq[Rune] =
  result = newSeq[Rune]()
  while (not stream.atEnd) and (stream.peekRune() notin " \t\nλ.()".toRunes()):
    result.add stream.readRune()

proc parseIdent(stream: Stream): Node =
  Node(kind: nkElem, elem: Elem(kind: ekIdent, id: parseIdentImpl(stream)))

proc parseFunc(stream: Stream): Node =
  # expect first to be a lambda
  assert stream.readRune() in [LAMBDA, "¦".runeAt(0)]
  stream.skip()
  let arg = parseIdentImpl(stream)
  stream.skip()
  assert stream.readRune() == '.'.Rune
  Node(kind: nkElem, elem:
    Elem(kind: ekFunc, arg: arg, body: stream.parseExpression))

proc parseExpression(stream: Stream): Node =
  var buff = newSeq[Node]()
  while `and`(not stream.atEnd(),
      stream.peekRune() notin "\n)".toRunes()):
    stream.skip()
    if stream.atEnd(): break
    case stream.peekRune()
    of LAMBDA, "¦".runeAt(0): buff.add stream.parseFunc()
    of '('.Rune:
      discard stream.readChar()
      let sexpr = stream.parseExpression()
      stream.skip()
      assert stream.readRune() == ')'.Rune
      buff.add sexpr
    else:
      buff.add stream.parseIdent()
  if buff.len == 1:
    return buff[0]
  result = Node(kind: nkTermin)
  for i in countdown(buff.len - 1, 0):
    result = Node(kind: nkLink, held: buff[i], next: result)

when defined(demo):
  let env = {
    "S".toRunes(): newStringStream("λf.λg.λx.(g x)(f x)").parseExpression(),
    "I".toRunes(): newStringStream("¦x.x").parseExpression()
  }.toTable

  var exp = newStringStream(" S I I ").parseExpression()
  echo fmt"[{exp.render}]"
  block:
    var res: Node = exp
    var prev: Node = exp
    var act: Action = Unpack
    while act != None:
      if act != None: echo fmt"=> {res.render}"
      (res, act) = res.modif(env)
      if act == Subbing:
        echo fmt"subbing({prev.kind})"
        echo fmt"   {prev.render} => {res.render}"
      prev = res
    exp = res
