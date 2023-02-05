import unicode, streams, tables
import os
import strformat

const LAMBDA = "λ".runeAt(0)
const LAMBAR = "¦".runeAt(0)

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

type Env = TableRef[seq[Rune], Node]

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
    if exp.elem.kind == ekIdent and exp.elem.id in env:
      return (env[exp.elem.id], Subbing)
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

func shape(node: Node): string =
  case node.kind
  of nkElem, nkTermin:
    $node.kind
  of nkLink:
   fmt"{node.kind}({node.held.kind}, {node.next.kind})"

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
  while (not stream.atEnd) and (stream.peekRune() notin " \t\nλ¦.()".toRunes()):
    result.add stream.readRune()

proc parseIdent(stream: Stream): Node =
  Node(kind: nkElem, elem: Elem(kind: ekIdent, id: parseIdentImpl(stream)))

proc parseFunc(stream: Stream): Node =
  # expect first to be a lambda
  assert stream.readRune() in [LAMBDA, LAMBAR]
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
    of LAMBDA, LAMBAR: buff.add stream.parseFunc()
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

proc solve(exp: Node, env: Env): Node =
  var res = exp
  var act = Unpack
  while act != None:
    echo fmt "{act}\t=> {res.render}"
#    echo fmt "{act}\t:: {shape(res)}"
    (res, act) = res.modif(env)
  return res

proc solveSlow(exp: Node, env: Env): Node =
  var res = exp
  var act = Unpack
  while act != None:
    echo fmt "{act}\t=> {res.render}"
#    echo fmt "{act}\t:: {shape(res)}"
    (res, act) = res.modif(env)
    sleep(33)
  return res

when defined(demo):
  let env: Env = {
    "S".toRunes(): newStringStream("λf.λg.λx.(g x)(f x)").parseExpression(),
    "K".toRunes(): newStringStream("λx.λy.x").parseExpression(),
    "I".toRunes(): newStringStream("¦x.x").parseExpression()
  }.newTable

  var exp = newStringStream("S (S K K) (S K K)").parseExpression()
  echo fmt"[{exp.render}]"
  discard solve(exp, env)

type
  StmtKind = enum
    skNone, skEval, skAssign, skConsist
  Stmt = ref object
    case kind: StmtKind
    of skNone: discard
    of skEval: exp: Node
    of skAssign, skConsist:
      target: seq[Rune]
      value: Node

proc parseStmt(stream: Stream): Stmt =
  stream.skip()
  while stream.peekChar() == '\n':
    if stream.atEnd():
      return Stmt(kind: skNone)
    discard stream.readChar()
    stream.skip()

  case stream.peekRune()
  of '('.Rune, LAMBDA, LAMBAR:
    result = Stmt(kind: skEval, exp: stream.parseExpression())
    stream.skip()
    assert stream.readChar() == '\n'
  else:
    let ident = stream.parseIdentImpl()
    stream.skip()
    case stream.peekChar()
    of ':':
      assert stream.readStr(3) == "::="
      stream.skip()
      result =  Stmt(kind: skConsist, target: ident, value: stream.parseExpression())
      stream.skip()
      assert stream.readChar() == '\n'
    of '=':
      discard stream.readChar()
      stream.skip()
      result =  Stmt(kind: skAssign, target: ident, value: stream.parseExpression())
      stream.skip()
      assert stream.readChar() == '\n'
    else:
      var tail = stream.parseExpression()
      if tail.kind == nkElem:
        tail = Node(kind: nkLink, held: tail, next: Node(kind: nkTermin))
      let held = Node(kind: nkElem, elem: Elem(kind: ekIdent, id: ident))
      result = Stmt(kind: skEval, exp: Node(kind: nkLink, held: held, next: tail))
      stream.skip()
      assert stream.readChar() == '\n'

func `$`(stm: Stmt): string =
  case stm.kind
  of skNone: "// Nothing"
  of skEval: stm.exp.render()
  of skAssign: fmt"{stm.target} = {stm.value.render}"
  of skConsist: fmt"{stm.target} ::= {stm.value.render}"

proc step(stream: Stream, env: var Env) =
  let stm = stream.parseStmt()
  echo "        ", stm
  case stm.kind
  of skNone: return
  of skEval:
    discard stm.exp.solveSlow(env)
  of skConsist:
    env[stm.target] = stm.value
  of skAssign:
    env[stm.target] = stm.value.solveSlow(env)
  echo "."

block:
  var inp = newStringStream("""
S ::= ¦f.¦g.¦x.(g x) (f x)
K ::= ¦x.¦y.x
I = S K K
M = S (S K K) (S K K)

M K I
""")
  var env: Env = newTable[seq[Rune], Node]()
  var sin = stdin.newFileStream
  while not inp.atEnd():
    inp.step(env)
    discard sin.readLine()

