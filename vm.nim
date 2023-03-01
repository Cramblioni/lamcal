
# implementing a more VM style approach in the same theme as  new-core

# based on de bruijn indexing, but with pointers rather than indexes.
# Indexes can be generated on the fly during rendering if needs be
# This does introduce a cyclic datastructure, though this should
# be treated as a cursor reference, As an argument shouldn't outlive
# it's respective function.

import strformat

type
  FuncId = distinct int
  ExprKind = enum
    ekArg, ekFunc, ekApply
  Expr = ref object
    case kind: ExprKind
    of ekArg:
      fnc: FuncId
    of ekFunc:
      fid: FuncId
      body: Expr
    of ekApply:
      targ: Expr
      value: Expr

func `==`(x, y: FuncId): bool =
  x.int == y.int

func build(exps: seq[Expr]): Expr =
  assert exps.len > 0
  result = exps[0]
  for i, x in exps:
    if i == 0: continue
    result = Expr(kind: ekApply, targ: result, value: x)

proc genid_impl: FuncId =
    var cur {. global .} = 0
    inc cur
    cur.FuncId

func genid: FuncId =
  {. cast(noSideEffect) .}: genid_impl()

func evalInt(inp: string; start, endp: Natural): int =
  result = 0
  for ind in start ..< endp:
    if inp[ind] notin "0123456789":
      break
    result = result * 10 + (inp[ind].int - '0'.int)

type
  ResultKind* = enum
    Error, Success
  Result*[E, S] = object
    case kind: ResultKind
    of Error:
      error: E
    of Success:
      value: S

func success*[E, S](value: S): Result[E, S] =
  Result[E, S](kind: Success, value: value)
func error*[E, S](error: E): Result[E, S] =
  Result[E, S](kind: Error, error: error)

template TRY*[E, T](res: Result[E, T]): T =
  let tmp = res
  case tmp.kind
  of Success:
    tmp.value
  of Error:
    return error[E, typeof(result.value)](tmp.error)

type 
  ParseErrorKind = enum
    IndexOutOfRange, ParenMismatch, UnexpectedChar
  ParseError = object
    kind: ParseErrorKind
    ind: int

func parseDeBruijn(source: string): Result[ParseError, Expr] =
  type
    FrameKind = enum
      BaseExpr, Func, Sub
    Frame = object
      start: int
      chunks: seq[Expr]
      case kind: FrameKind
      of Func: id: FuncId
      else: discard
  var
    stack = newSeqOfCap[Frame](32)
    fids  = newSeqOfCap[FuncId](32)
  template popFrame(): Frame =
    if stack[^1].kind == Func: discard fids.pop()
    stack.pop()
  template pushFrame(fkind: FrameKind) =
    var tmp = Frame(kind: fkind, chunks: newSeq[Expr](), start: cind)
    if fkind == Func:
      tmp.id = genid()
      fids.add tmp.id
    stack.add tmp
  var cind = 0
  template atEnd: bool = cind >= source.len
  template peek: char  = source[cind]
  template step: char  = (let tmp = source[cind]; inc cind; tmp)
  template skip        = inc cind
  pushFrame(BaseExpr)
  while not atEnd:
    case step()
    of ' ', '\t':
      continue
    of '0' .. '9':
      let start = cind - 1
      while not atEnd and peek() in "0123456789": skip()
      let ind = evalInt(source, start, cind)
      if ind >= fids.len:
        return error[ParseError, Expr](ParseError(kind: IndexOutOfRange, ind: start))
      stack[^1].chunks.add Expr(kind: ekArg, fnc: fids[fids.len - (ind + 1)])
    of '/':
      pushFrame(Func)
    of '(':
      pushFrame(Sub)
    of ')':
      var cur = popFrame()
      while true:
        if cur.kind == BaseExpr:
          return error[ParseError, Expr](ParseError(kind: ParenMismatch, ind: cind - 1))
        elif cur.kind == Sub: break
        stack[^1].chunks.add Expr(kind: ekFunc, fid: cur.id, body: cur.chunks.build())
        cur = popFrame()
      stack[^1].chunks.add cur.chunks.build()
    else:
      return error[ParseError, Expr](ParseError(kind: UnexpectedChar, ind: cind - 1))
  var cur = popFrame()
  while cur.kind != BaseExpr:
    if cur.kind == Sub:
      return error[ParseError, Expr](ParseError(kind: ParenMismatch, ind: cind))
    stack[^1].chunks.add Expr(kind: ekFunc, fid: cur.id, body: cur.chunks.build())
    cur = popFrame()
  return success[ParseError, Expr](cur.chunks.build())

func depth(cur: Expr): int =
      var reg = cur
      result = 1
      while reg.kind == ekApply:
        inc result
        reg = reg.targ

func unpack(exp: Expr): seq[Expr] =
  result = newSeq[Expr](depth(exp))
  var
    acc = exp
  for i in countdown(result.len - 1, 1):
    result[i] = acc.value
    acc = acc.targ
  result[0] = acc

func seamlessJoin(strs: seq[string]): string =
  var slen = 0
  for s in strs: slen += s.len
  result = newStringOfCap(slen)
  for s in strs:
    for c in s:
      result.add c

func renderDeBruijn(exp: Expr): string =
  type
    Task = object
      uexp: seq[Expr]
      outp: seq[string]
      ind: int
  var
    fids  = newSeqOfCap[FuncId](exp.depth)
    stack = newSeqOfCap[Task](32)
  template pushTask(exp: Expr) =
    let uexp = exp.unpack
    stack.add Task(uexp: uexp, ind: 0, outp: newSeq[string](uexp.len))
  template popTask: Task =
    stack.pop()
  pushTask(exp)
  while stack.len > 0:
    if stack[^1].ind > stack[^1].uexp.len:
      debugEcho "squashing"
      if stack.len == 1: break
      let
        cur = stack.pop()
        tind = stack[^1].ind - 1
        base = stack[^1].uexp[tind]
      # TODO: implement placing shit
      case base.kind
      of ekArg: # inaccessible
        assert false
      of ekApply:
        stack[^1].outp[tind] = "(" & cur.outp.seamlessJoin & ")"
      of ekFunc:
        if tind == stack[^1].ind - 1:
          stack[^1].outp[tind] = "λ" & cur.outp.seamlessJoin
        else:
          stack[^1].outp[tind] = "(λ" & cur.outp.seamlessJoin & ")"
    else:
      debugEcho fmt"rendering @ {stack[^1].ind} : {stack[^1].uexp.len}"
      let cur = stack[^1].uexp[stack[^1].ind]
      inc stack[^1].ind
      case cur.kind
      of ekArg:
        stack[^1].outp[stack[^1].ind] = $(fids.len - fids.find(cur.fnc))
      of ekFunc:
        fids.add cur.fid
        pushTask(cur.body)
      of ekApply:
        pushTask(cur)
  assert stack.len == 1
  return seamlessJoin(stack[0].outp)

func renderShape(exp: Expr): string =
  case exp.kind
  of ekArg: "Arg"
  of ekApply:
    let all = unpack(exp)
    if all.len() == 0:
      return "<ERROR Apply>"
    var buff = newSeq[string](all.len * 2 - 1)
    for i, sexpr in all:
      buff[i * 2] = renderShape(sexpr)
      if i < all.len - 1: buff[i * 2 + 1] = ", "
    fmt"Apply[{buff.seamlessJoin}]"
  of ekFunc: fmt"Func[{exp.body.renderShape}]"

when isMainModule:
  let tmp = parseDeBruijn("/ (//1) 0 0")
  echo seamlessJoin(@["testing ", "seam", "less join"])
  echo tmp
  if tmp.kind == Success:
    echo renderShape(tmp.value)
    echo renderDeBruijn(tmp.value)
