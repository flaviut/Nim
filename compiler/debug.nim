import ast, strutils, ropes, msgs
from rodutils import toStrMaxPrecision

proc lineInfoToStr*(info: TLineInfo): Rope
# these are for debugging only: They are not really deprecated, but I want
# the warning so that release versions do not contain debugging statements:
proc debug*(n: PSym) {.deprecated.}
proc debug*(n: PType) {.deprecated.}
proc debug*(n: PNode) {.deprecated.}


proc rspaces(x: int): Rope =
  # returns x spaces
  result = rope(spaces(x))

proc lineInfoToStr(info: TLineInfo): Rope =
  result = "[$1, $2, $3]" % [rope(escape(toFilename(info))),
                             rope(toLinenumber(info)),
                             rope(toColumn(info))]


proc ropeConstr(indent: int, c: openArray[Rope]): Rope =
  # array of (name, value) pairs
  var istr = rspaces(indent + 2)
  result = rope("{")
  var i = 0
  while i <= high(c):
    if i > 0: add(result, ",")
    addf(result, "$N$1\"$2\": $3", [istr, c[i], c[i + 1]])
    inc(i, 2)
  addf(result, "$N$1}", [rspaces(indent)])


proc debugTree*(n: PNode, indent: int, maxRecDepth: int; renderType=false): Rope
proc debugType(n: PType, maxRecDepth=100): Rope =
  if n == nil:
    result = rope("null")
  else:
    result = rope($n.kind)
    if n.sym != nil:
      add(result, " ")
      add(result, n.sym.name.s)
    if n.kind in IntegralTypes and n.n != nil:
      add(result, ", node: ")
      add(result, debugTree(n.n, 2, maxRecDepth-1, renderType=true))
    if (n.kind != tyString) and (sonsLen(n) > 0) and maxRecDepth != 0:
      add(result, "(")
      for i in countup(0, sonsLen(n) - 1):
        if i > 0: add(result, ", ")
        if n.sons[i] == nil:
          add(result, "null")
        else:
          add(result, debugType(n.sons[i], maxRecDepth-1))
      if n.kind == tyObject and n.n != nil:
        add(result, ", node: ")
        add(result, debugTree(n.n, 2, maxRecDepth-1, renderType=true))
      add(result, ")")

proc debugTree(n: PNode, indent: int, maxRecDepth: int;
               renderType=false): Rope =
  if n == nil:
    result = rope("null")
  else:
    var istr = rspaces(indent + 2)
    result = "{$N$1\"kind\": $2" %
             [istr, rope(escape($n.kind))]
    if maxRecDepth != 0:
      case n.kind
      of nkCharLit..nkUInt64Lit:
        addf(result, ",$N$1\"intVal\": $2", [istr, rope(n.intVal)])
      of nkFloatLit, nkFloat32Lit, nkFloat64Lit:
        addf(result, ",$N$1\"floatVal\": $2",
            [istr, rope(n.floatVal.toStrMaxPrecision)])
      of nkStrLit..nkTripleStrLit:
        if n.strVal.isNil:
          addf(result, ",$N$1\"strVal\": null", [istr])
        else:
          addf(result, ",$N$1\"strVal\": $2", [istr, rope(escape(n.strVal))])
      of nkSym:
        addf(result, ",$N$1\"sym\": $2_$3",
            [istr, rope(n.sym.name.s), rope(n.sym.id)])
        if renderType and n.sym.typ != nil:
          addf(result, ",$N$1\"typ\": $2", [istr, debugType(n.sym.typ, 2)])
      of nkIdent:
        if n.ident != nil:
          addf(result, ",$N$1\"ident\": $2", [istr, rope(escape(n.ident.s))])
        else:
          addf(result, ",$N$1\"ident\": null", [istr])
      else:
        if sonsLen(n) > 0:
          addf(result, ",$N$1\"sons\": [", [istr])
          for i in countup(0, sonsLen(n) - 1):
            if i > 0: add(result, ",")
            addf(result, "$N$1$2", [rspaces(indent + 4), debugTree(n.sons[i],
                indent + 4, maxRecDepth - 1, renderType)])
          addf(result, "$N$1]", [istr])
    addf(result, ",$N$1\"info\": $2", [istr, lineInfoToStr(n.info)])
    addf(result, "$N$1}", [rspaces(indent)])

proc debug(n: PSym) =
  if n == nil:
    msgWriteln("null")
  elif n.kind == skUnknown:
    msgWriteln("skUnknown")
  else:
    msgWriteln("$1_$2: $3, $4, $5, $6" % [
      n.name.s, $n.id, $n.flags, $n.loc.flags, $lineInfoToStr(n.info), $n.kind])

proc debug(n: PType) =
  msgWriteln($debugType(n))

proc debug(n: PNode) =
  msgWriteln($debugTree(n, 0, 100))
