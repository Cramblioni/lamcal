
# implementing a more VM style approach in the same theme as  new-core

# based on de bruijn indexing, but with pointers rather than indexes.
# Indexes can be generated on the fly during rendering if needs be
# This does introduce a cyclic datastructure, though this should
# be treated as a cursor reference, As an argument shouldn't outlive
# it's respective function.

import std/[strformat, tables, os, macros, strutils]

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
macro slet(x: typedesc, i: static int): untyped =
  getTypeImpl(x)[1][i + 1]

func success*[E, S](value: S): Result[E, S] =
  Result[E, S](kind: Success, value: value)
func success*[E](): Result[E, void] =
  Result[E, void](kind: Success)
func error*[E, S](error: E): Result[E, S] =
  Result[E, S](kind: Error, error: error)

template TRY*[E, T](res: Result[E, T]): T =
  let tmp = res
  case tmp.kind
  of Success:
    when T is void:
      discard
    else:
      tmp.value
  of Error:
    # macro thingy [genericParams(result.type)[1]]
    return error[E, slet(result.type, 1)](tmp.error)

type 
  ParseErrorKind = enum
    IndexOutOfRange, ParenMismatch, UnexpectedChar
    UndefinedIdent
  ParseError = object
    ind: int
    case kind: ParseErrorKind
    of IndexOutOfRange:
      inv: int
    of UndefinedIdent:
      ident: string
    else: discard
    

func parseDeBruijn(source: string, env=newTable[string, Expr]()): Result[ParseError, Expr] =
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
        return error[ParseError, Expr](ParseError(kind: IndexOutOfRange, ind: start, inv: ind))
      stack[^1].chunks.add Expr(kind: ekArg, fnc: fids[fids.len - (ind + 1)])
    of '`':
      let start = cind
      while not atEnd and peek() notin " /)(`": skip()
      let ident = source[start ..< cind]
      if ident notin env:
        return error[ParseError, Expr](ParseError(kind: UndefinedIdent, ind: start - 1,
                                                  ident: ident))
      stack[^1].chunks.add env[ident]
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
    # debugEcho "Pushing Task ", exp.renderShape
    let uexp = exp.unpack
    stack.add Task(uexp: uexp, ind: 0, outp: newSeq[string](uexp.len + 1))
  template popTask: Task =
    stack.pop()
  template head: Task =
    stack[^1]
  pushTask(exp)
  while stack.len > 0:
    if head.ind >= head.uexp.len:
      # debugEcho "squashing"
      if stack.len == 1: break
      let
        cur = stack.pop()
        tind = head.ind - 1
        base = head.uexp[tind]
      # TODO: implement placing shit
      case base.kind
      of ekArg: # inaccessible
        assert false
      of ekApply:
        head.outp[tind] = "(" & cur.outp.seamlessJoin & ")"
      of ekFunc:
        discard fids.pop()
        let atend = head.ind >= head.uexp.len 
        head.outp[tind] = (if atend:
            "λ" & cur.outp.seamlessJoin
          else:
            "(λ" & cur.outp.seamlessJoin & ")")
    else:
      # debugEcho fmt"rendering @ {head.ind} : {head.uexp.len}"
      let cur = head.uexp[head.ind]
      inc head.ind
      case cur.kind
      of ekArg:
        head.outp[head.ind - 1] = $(fids.len - fids.find(cur.fnc) - 1) & " "
      of ekFunc:
        fids.add cur.fid
        pushTask(cur.body)
      of ekApply:
        pushTask(cur)
  assert stack.len == 1
  return seamlessJoin(stack[0].outp)

func subst(base: Expr, id: FuncId, value: Expr): Expr =
  case base.kind
  of ekArg:
    if base.fnc == id: value
    else: base
  of ekFunc:
    Expr(kind: ekFunc, fid: base.fid, body: base.body.subst(id, value))
  of ekApply:
    Expr(kind: ekApply, targ: base.targ.subst(id, value),
                       value: base.value.subst(id, value))

type Action = enum
  Nothing, BetaReduction, Start

func modifMid(exp: Expr): tuple[res: Expr, act: Action]
func modif(exp: Expr): tuple[res: Expr, act: Action] =
  # we want this to continue onto a alt of this
  case exp.kind
  of ekApply:
    if exp.targ.kind == ekFunc:
      (exp.targ.body.subst(exp.targ.fid, exp.value), BetaReduction)
    else:
      modifMid(exp)
  else:
    modifMid(exp)

func modifMid(exp: Expr): tuple[res: Expr, act: Action] =
  case exp.kind
  of ekApply:
    if exp.targ.kind == ekApply:
      let (res, act) = modif(exp.targ)
      (Expr(kind: ekApply, targ: res, value: exp.value), act)
    else:
      let (res, act) = modif(exp.value)
      (Expr(kind: ekApply, targ: exp.targ, value: res), act)
  of ekFunc:
    let (res, act) = modif(exp.body)
    (Expr(kind: ekFunc, fid: exp.fid, body: res), act)
  else:
    (exp, Nothing)

proc solve(exp: Expr, slow: static bool = false): Expr =
  var act = Start
  result = exp
  while act != Nothing:
    (result, act) = result.modif
    echo fmt"{act} : {result.renderDeBruijn}"
    when slow: sleep(50)

proc interpDeBruijn(source: string): Result[ParseError, void] =
  result = success[ParseError]()
  var env = newTable[string, Expr]()
  for line in source.splitLines:
    if line == "": continue
    discard solve(TRY parseDeBruijn(line))

when isMainModule:
  # let tmp = parseDeBruijn("(////3 1 (2 1 0)) (//1(1(1(1 0)))) (//1 0)")
  let tmp = interpDeBruijn("(///0 2 1) (//0) (//1 0)")
  case tmp.kind
  of Error:
    echo tmp.error
  of Success:
    echo "Done"
