#
#
#           The Nim Compiler
#        (c) Copyright 2012 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# Algorithms for the abstract syntax tree: hash tables, lists
# and sets of nodes are supported. Efficiency is important as
# the data structures here are used in various places of the compiler.

import
  ast, hashes, intsets, strutils, options, msgs, ropes, idents, rodutils

proc hashNode*(p: RootRef): THash

# ----------------------- node sets: ---------------------------------------
proc objectSetContains*(t: TObjectSet, obj: RootRef): bool
  # returns true whether n is in t
proc objectSetIncl*(t: var TObjectSet, obj: RootRef)
  # include an element n in the table t
proc objectSetContainsOrIncl*(t: var TObjectSet, obj: RootRef): bool
  # more are not needed ...

# ----------------------- (key, val)-Hashtables ----------------------------
proc tablePut*(t: var TTable, key, val: RootRef)
proc tableGet*(t: TTable, key: RootRef): RootRef
type
  TCmpProc* = proc (key, closure: RootRef): bool {.nimcall.} # true if found

proc tableSearch*(t: TTable, key, closure: RootRef,
                  comparator: TCmpProc): RootRef
  # return val as soon as comparator returns true; if this never happens,
  # nil is returned

# ----------------------- str table -----------------------------------------
proc strTableContains*(t: TStrTable, n: PSym): bool
proc strTableAdd*(t: var TStrTable, n: PSym)
proc strTableGet*(t: TStrTable, name: PIdent): PSym

type
  TTabIter*{.final.} = object # consider all fields here private
    h*: THash                 # current hash

proc initTabIter*(ti: var TTabIter, tab: TStrTable): PSym
proc nextIter*(ti: var TTabIter, tab: TStrTable): PSym
  # usage:
  # var
  #   i: TTabIter
  #   s: PSym
  # s = InitTabIter(i, table)
  # while s != nil:
  #   ...
  #   s = NextIter(i, table)
  #

type
  TIdentIter*{.final.} = object # iterator over all syms with same identifier
    h*: THash                   # current hash
    name*: PIdent


proc initIdentIter*(ti: var TIdentIter, tab: TStrTable, s: PIdent): PSym
proc nextIdentIter*(ti: var TIdentIter, tab: TStrTable): PSym

# --------------------------- ident tables ----------------------------------
proc idTableGet*(t: TIdTable, key: PIdObj): RootRef
proc idTableGet*(t: TIdTable, key: int): RootRef
proc idTablePut*(t: var TIdTable, key: PIdObj, val: RootRef)
proc idTableHasObjectAsKey*(t: TIdTable, key: PIdObj): bool
  # checks if `t` contains the `key` (compared by the pointer value, not only
  # `key`'s id)
proc idNodeTableGet*(t: TIdNodeTable, key: PIdObj): PNode
proc idNodeTablePut*(t: var TIdNodeTable, key: PIdObj, val: PNode)

# ---------------------------------------------------------------------------

proc getSymFromList*(list: PNode, ident: PIdent, start: int = 0): PSym
proc lookupInRecord*(n: PNode, field: PIdent): PSym
proc getModule*(s: PSym): PSym
proc mustRehash*(length, counter: int): bool
proc nextTry*(h, maxHash: THash): THash {.inline.}

# ------------- table[int, int] ---------------------------------------------
const
  InvalidKey* = low(int)

type
  TIIPair*{.final.} = object
    key*, val*: int

  TIIPairSeq* = seq[TIIPair]
  TIITable*{.final.} = object # table[int, int]
    counter*: int
    data*: TIIPairSeq


proc initIiTable*(x: var TIITable)
proc iiTableGet*(t: TIITable, key: int): int
proc iiTablePut*(t: var TIITable, key, val: int)

# implementation

proc skipConvAndClosure*(n: PNode): PNode =
  result = n
  while true:
    case result.kind
    of nkObjUpConv, nkObjDownConv, nkChckRange, nkChckRangeF, nkChckRange64,
       nkClosure:
      result = result.sons[0]
    of nkHiddenStdConv, nkHiddenSubConv, nkConv:
      result = result.sons[1]
    else: break

proc sameValue*(a, b: PNode): bool =
  result = false
  case a.kind
  of nkCharLit..nkUInt64Lit:
    if b.kind in {nkCharLit..nkUInt64Lit}: result = a.intVal == b.intVal
  of nkFloatLit..nkFloat64Lit:
    if b.kind in {nkFloatLit..nkFloat64Lit}: result = a.floatVal == b.floatVal
  of nkStrLit..nkTripleStrLit:
    if b.kind in {nkStrLit..nkTripleStrLit}: result = a.strVal == b.strVal
  else:
    # don't raise an internal error for 'nimrod check':
    #InternalError(a.info, "SameValue")
    discard

proc leValue*(a, b: PNode): bool =
  # a <= b?
  result = false
  case a.kind
  of nkCharLit..nkUInt32Lit:
    if b.kind in {nkCharLit..nkUInt32Lit}: result = a.intVal <= b.intVal
  of nkFloatLit..nkFloat64Lit:
    if b.kind in {nkFloatLit..nkFloat64Lit}: result = a.floatVal <= b.floatVal
  of nkStrLit..nkTripleStrLit:
    if b.kind in {nkStrLit..nkTripleStrLit}: result = a.strVal <= b.strVal
  else:
    # don't raise an internal error for 'nimrod check':
    #InternalError(a.info, "leValue")
    discard

proc weakLeValue*(a, b: PNode): TImplication =
  if a.kind notin nkLiterals or b.kind notin nkLiterals:
    result = impUnknown
  else:
    result = if leValue(a, b): impYes else: impNo

proc lookupInRecord(n: PNode, field: PIdent): PSym =
  result = nil
  case n.kind
  of nkRecList:
    for i in countup(0, sonsLen(n) - 1):
      result = lookupInRecord(n.sons[i], field)
      if result != nil: return
  of nkRecCase:
    if (n.sons[0].kind != nkSym): internalError(n.info, "lookupInRecord")
    result = lookupInRecord(n.sons[0], field)
    if result != nil: return
    for i in countup(1, sonsLen(n) - 1):
      case n.sons[i].kind
      of nkOfBranch, nkElse:
        result = lookupInRecord(lastSon(n.sons[i]), field)
        if result != nil: return
      else: internalError(n.info, "lookupInRecord(record case branch)")
  of nkSym:
    if n.sym.name.id == field.id: result = n.sym
  else: internalError(n.info, "lookupInRecord()")

proc getModule(s: PSym): PSym =
  result = s
  assert((result.kind == skModule) or (result.owner != result))
  while result != nil and result.kind != skModule: result = result.owner

proc getSymFromList(list: PNode, ident: PIdent, start: int = 0): PSym =
  for i in countup(start, sonsLen(list) - 1):
    if list.sons[i].kind == nkSym:
      result = list.sons[i].sym
      if result.name.id == ident.id: return
    else: internalError(list.info, "getSymFromList")
  result = nil

proc hashNode(p: RootRef): THash =
  result = hash(cast[pointer](p))

proc mustRehash(length, counter: int): bool =
  assert(length > counter)
  result = (length * 2 < counter * 3) or (length - counter < 4)

const
  EmptySeq = @[]

proc nextTry(h, maxHash: THash): THash =
  result = ((5 * h) + 1) and maxHash
  # For any initial h in range(maxHash), repeating that maxHash times
  # generates each int in range(maxHash) exactly once (see any text on
  # random-number generation for proof).

proc objectSetContains(t: TObjectSet, obj: RootRef): bool =
  # returns true whether n is in t
  var h: THash = hashNode(obj) and high(t.data) # start with real hash value
  while t.data[h] != nil:
    if t.data[h] == obj:
      return true
    h = nextTry(h, high(t.data))
  result = false

proc objectSetRawInsert(data: var TObjectSeq, obj: RootRef) =
  var h: THash = hashNode(obj) and high(data)
  while data[h] != nil:
    assert(data[h] != obj)
    h = nextTry(h, high(data))
  assert(data[h] == nil)
  data[h] = obj

proc objectSetEnlarge(t: var TObjectSet) =
  var n: TObjectSeq
  newSeq(n, len(t.data) * GrowthFactor)
  for i in countup(0, high(t.data)):
    if t.data[i] != nil: objectSetRawInsert(n, t.data[i])
  swap(t.data, n)

proc objectSetIncl(t: var TObjectSet, obj: RootRef) =
  if mustRehash(len(t.data), t.counter): objectSetEnlarge(t)
  objectSetRawInsert(t.data, obj)
  inc(t.counter)

proc objectSetContainsOrIncl(t: var TObjectSet, obj: RootRef): bool =
  # returns true if obj is already in the string table:
  var h: THash = hashNode(obj) and high(t.data)
  while true:
    var it = t.data[h]
    if it == nil: break
    if it == obj:
      return true             # found it
    h = nextTry(h, high(t.data))
  if mustRehash(len(t.data), t.counter):
    objectSetEnlarge(t)
    objectSetRawInsert(t.data, obj)
  else:
    assert(t.data[h] == nil)
    t.data[h] = obj
  inc(t.counter)
  result = false

proc tableRawGet(t: TTable, key: RootRef): int =
  var h: THash = hashNode(key) and high(t.data) # start with real hash value
  while t.data[h].key != nil:
    if t.data[h].key == key:
      return h
    h = nextTry(h, high(t.data))
  result = -1

proc tableSearch(t: TTable, key, closure: RootRef,
                 comparator: TCmpProc): RootRef =
  var h: THash = hashNode(key) and high(t.data) # start with real hash value
  while t.data[h].key != nil:
    if t.data[h].key == key:
      if comparator(t.data[h].val, closure):
        # BUGFIX 1
        return t.data[h].val
    h = nextTry(h, high(t.data))
  result = nil

proc tableGet(t: TTable, key: RootRef): RootRef =
  var index = tableRawGet(t, key)
  if index >= 0: result = t.data[index].val
  else: result = nil

proc tableRawInsert(data: var TPairSeq, key, val: RootRef) =
  var h: THash = hashNode(key) and high(data)
  while data[h].key != nil:
    assert(data[h].key != key)
    h = nextTry(h, high(data))
  assert(data[h].key == nil)
  data[h].key = key
  data[h].val = val

proc tableEnlarge(t: var TTable) =
  var n: TPairSeq
  newSeq(n, len(t.data) * GrowthFactor)
  for i in countup(0, high(t.data)):
    if t.data[i].key != nil: tableRawInsert(n, t.data[i].key, t.data[i].val)
  swap(t.data, n)

proc tablePut(t: var TTable, key, val: RootRef) =
  var index = tableRawGet(t, key)
  if index >= 0:
    t.data[index].val = val
  else:
    if mustRehash(len(t.data), t.counter): tableEnlarge(t)
    tableRawInsert(t.data, key, val)
    inc(t.counter)

proc strTableContains(t: TStrTable, n: PSym): bool =
  var h: THash = n.name.h and high(t.data) # start with real hash value
  while t.data[h] != nil:
    if (t.data[h] == n):
      return true
    h = nextTry(h, high(t.data))
  result = false

proc strTableRawInsert(data: var TSymSeq, n: PSym) =
  var h: THash = n.name.h and high(data)
  if sfImmediate notin n.flags:
    # fast path:
    while data[h] != nil:
      if data[h] == n:
        # allowed for 'export' feature:
        #InternalError(n.info, "StrTableRawInsert: " & n.name.s)
        return
      h = nextTry(h, high(data))
    assert(data[h] == nil)
    data[h] = n
  else:
    # slow path; we have to ensure immediate symbols are preferred for
    # symbol lookups.
    # consider the chain: foo (immediate), foo, bar, bar (immediate)
    # then bar (immediate) gets replaced with foo (immediate) and the non
    # immediate foo is picked! Thus we need to replace it with the first
    # slot that has in fact the same identifier stored in it!
    var favPos = -1
    while data[h] != nil:
      if data[h] == n: return
      if favPos < 0 and data[h].name.id == n.name.id: favPos = h
      h = nextTry(h, high(data))
    assert(data[h] == nil)
    data[h] = n
    if favPos >= 0: swap data[h], data[favPos]

proc symTabReplaceRaw(data: var TSymSeq, prevSym: PSym, newSym: PSym) =
  assert prevSym.name.h == newSym.name.h
  var h: THash = prevSym.name.h and high(data)
  while data[h] != nil:
    if data[h] == prevSym:
      data[h] = newSym
      return
    h = nextTry(h, high(data))
  assert false

proc symTabReplace*(t: var TStrTable, prevSym: PSym, newSym: PSym) =
  symTabReplaceRaw(t.data, prevSym, newSym)

proc strTableEnlarge(t: var TStrTable) =
  var n: TSymSeq
  newSeq(n, len(t.data) * GrowthFactor)
  for i in countup(0, high(t.data)):
    if t.data[i] != nil: strTableRawInsert(n, t.data[i])
  swap(t.data, n)

proc strTableAdd(t: var TStrTable, n: PSym) =
  if mustRehash(len(t.data), t.counter): strTableEnlarge(t)
  strTableRawInsert(t.data, n)
  inc(t.counter)

proc reallySameIdent(a, b: string): bool {.inline.} =
  when defined(nimfix):
    result = a[0] == b[0]
  else:
    result = true

proc strTableIncl*(t: var TStrTable, n: PSym): bool {.discardable.} =
  # returns true if n is already in the string table:
  # It is essential that `n` is written nevertheless!
  # This way the newest redefinition is picked by the semantic analyses!
  assert n.name != nil
  var h: THash = n.name.h and high(t.data)
  var replaceSlot = -1
  while true:
    var it = t.data[h]
    if it == nil: break
    # Semantic checking can happen multiple times thanks to templates
    # and overloading: (var x=@[]; x).mapIt(it).
    # So it is possible the very same sym is added multiple
    # times to the symbol table which we allow here with the 'it == n' check.
    if it.name.id == n.name.id and reallySameIdent(it.name.s, n.name.s):
      if it == n: return false
      replaceSlot = h
    h = nextTry(h, high(t.data))
  if replaceSlot >= 0:
    t.data[replaceSlot] = n # overwrite it with newer definition!
    return true             # found it
  elif mustRehash(len(t.data), t.counter):
    strTableEnlarge(t)
    strTableRawInsert(t.data, n)
  else:
    assert(t.data[h] == nil)
    t.data[h] = n
  inc(t.counter)
  result = false

proc strTableGet(t: TStrTable, name: PIdent): PSym =
  var h: THash = name.h and high(t.data)
  while true:
    result = t.data[h]
    if result == nil: break
    if result.name.id == name.id: break
    h = nextTry(h, high(t.data))

proc initIdentIter(ti: var TIdentIter, tab: TStrTable, s: PIdent): PSym =
  ti.h = s.h
  ti.name = s
  if tab.counter == 0: result = nil
  else: result = nextIdentIter(ti, tab)

proc nextIdentIter(ti: var TIdentIter, tab: TStrTable): PSym =
  var h = ti.h and high(tab.data)
  var start = h
  result = tab.data[h]
  while result != nil:
    if result.name.id == ti.name.id: break
    h = nextTry(h, high(tab.data))
    if h == start:
      result = nil
      break
    result = tab.data[h]
  ti.h = nextTry(h, high(tab.data))

proc nextIdentExcluding*(ti: var TIdentIter, tab: TStrTable,
                         excluding: IntSet): PSym =
  var h: THash = ti.h and high(tab.data)
  var start = h
  result = tab.data[h]
  while result != nil:
    if result.name.id == ti.name.id and not contains(excluding, result.id):
      break
    h = nextTry(h, high(tab.data))
    if h == start:
      result = nil
      break
    result = tab.data[h]
  ti.h = nextTry(h, high(tab.data))
  if result != nil and contains(excluding, result.id): result = nil

proc firstIdentExcluding*(ti: var TIdentIter, tab: TStrTable, s: PIdent,
                          excluding: IntSet): PSym =
  ti.h = s.h
  ti.name = s
  if tab.counter == 0: result = nil
  else: result = nextIdentExcluding(ti, tab, excluding)

proc initTabIter(ti: var TTabIter, tab: TStrTable): PSym =
  ti.h = 0                    # we start by zero ...
  if tab.counter == 0:
    result = nil              # FIX 1: removed endless loop
  else:
    result = nextIter(ti, tab)

proc nextIter(ti: var TTabIter, tab: TStrTable): PSym =
  result = nil
  while (ti.h <= high(tab.data)):
    result = tab.data[ti.h]
    inc(ti.h)                 # ... and increment by one always
    if result != nil: break

iterator items*(tab: TStrTable): PSym =
  var it: TTabIter
  var s = initTabIter(it, tab)
  while s != nil:
    yield s
    s = nextIter(it, tab)

proc hasEmptySlot(data: TIdPairSeq): bool =
  for h in countup(0, high(data)):
    if data[h].key == nil:
      return true
  result = false

proc idTableRawGet(t: TIdTable, key: int): int =
  var h: THash
  h = key and high(t.data)    # start with real hash value
  while t.data[h].key != nil:
    if t.data[h].key.id == key:
      return h
    h = nextTry(h, high(t.data))
  result = - 1

proc idTableHasObjectAsKey(t: TIdTable, key: PIdObj): bool =
  var index = idTableRawGet(t, key.id)
  if index >= 0: result = t.data[index].key == key
  else: result = false

proc idTableGet(t: TIdTable, key: PIdObj): RootRef =
  var index = idTableRawGet(t, key.id)
  if index >= 0: result = t.data[index].val
  else: result = nil

proc idTableGet(t: TIdTable, key: int): RootRef =
  var index = idTableRawGet(t, key)
  if index >= 0: result = t.data[index].val
  else: result = nil

iterator pairs*(t: TIdTable): tuple[key: int, value: RootRef] =
  for i in 0..high(t.data):
    if t.data[i].key != nil:
      yield (t.data[i].key.id, t.data[i].val)

proc idTableRawInsert(data: var TIdPairSeq, key: PIdObj, val: RootRef) =
  var h: THash
  h = key.id and high(data)
  while data[h].key != nil:
    assert(data[h].key.id != key.id)
    h = nextTry(h, high(data))
  assert(data[h].key == nil)
  data[h].key = key
  data[h].val = val

proc idTablePut(t: var TIdTable, key: PIdObj, val: RootRef) =
  var
    index: int
    n: TIdPairSeq
  index = idTableRawGet(t, key.id)
  if index >= 0:
    assert(t.data[index].key != nil)
    t.data[index].val = val
  else:
    if mustRehash(len(t.data), t.counter):
      newSeq(n, len(t.data) * GrowthFactor)
      for i in countup(0, high(t.data)):
        if t.data[i].key != nil:
          idTableRawInsert(n, t.data[i].key, t.data[i].val)
      assert(hasEmptySlot(n))
      swap(t.data, n)
    idTableRawInsert(t.data, key, val)
    inc(t.counter)

iterator idTablePairs*(t: TIdTable): tuple[key: PIdObj, val: RootRef] =
  for i in 0 .. high(t.data):
    if not isNil(t.data[i].key): yield (t.data[i].key, t.data[i].val)

proc idNodeTableRawGet(t: TIdNodeTable, key: PIdObj): int =
  var h: THash
  h = key.id and high(t.data) # start with real hash value
  while t.data[h].key != nil:
    if t.data[h].key.id == key.id:
      return h
    h = nextTry(h, high(t.data))
  result = - 1

proc idNodeTableGet(t: TIdNodeTable, key: PIdObj): PNode =
  var index: int
  index = idNodeTableRawGet(t, key)
  if index >= 0: result = t.data[index].val
  else: result = nil

proc idNodeTableGetLazy*(t: TIdNodeTable, key: PIdObj): PNode =
  if not isNil(t.data):
    result = idNodeTableGet(t, key)

proc idNodeTableRawInsert(data: var TIdNodePairSeq, key: PIdObj, val: PNode) =
  var h: THash
  h = key.id and high(data)
  while data[h].key != nil:
    assert(data[h].key.id != key.id)
    h = nextTry(h, high(data))
  assert(data[h].key == nil)
  data[h].key = key
  data[h].val = val

proc idNodeTablePut(t: var TIdNodeTable, key: PIdObj, val: PNode) =
  var index = idNodeTableRawGet(t, key)
  if index >= 0:
    assert(t.data[index].key != nil)
    t.data[index].val = val
  else:
    if mustRehash(len(t.data), t.counter):
      var n: TIdNodePairSeq
      newSeq(n, len(t.data) * GrowthFactor)
      for i in countup(0, high(t.data)):
        if t.data[i].key != nil:
          idNodeTableRawInsert(n, t.data[i].key, t.data[i].val)
      swap(t.data, n)
    idNodeTableRawInsert(t.data, key, val)
    inc(t.counter)

proc idNodeTablePutLazy*(t: var TIdNodeTable, key: PIdObj, val: PNode) =
  if isNil(t.data): initIdNodeTable(t)
  idNodeTablePut(t, key, val)

iterator pairs*(t: TIdNodeTable): tuple[key: PIdObj, val: PNode] =
  for i in 0 .. high(t.data):
    if not isNil(t.data[i].key): yield (t.data[i].key, t.data[i].val)

proc initIITable(x: var TIITable) =
  x.counter = 0
  newSeq(x.data, StartSize)
  for i in countup(0, StartSize - 1): x.data[i].key = InvalidKey

proc iiTableRawGet(t: TIITable, key: int): int =
  var h: THash
  h = key and high(t.data)    # start with real hash value
  while t.data[h].key != InvalidKey:
    if t.data[h].key == key: return h
    h = nextTry(h, high(t.data))
  result = -1

proc iiTableGet(t: TIITable, key: int): int =
  var index = iiTableRawGet(t, key)
  if index >= 0: result = t.data[index].val
  else: result = InvalidKey

proc iiTableRawInsert(data: var TIIPairSeq, key, val: int) =
  var h: THash
  h = key and high(data)
  while data[h].key != InvalidKey:
    assert(data[h].key != key)
    h = nextTry(h, high(data))
  assert(data[h].key == InvalidKey)
  data[h].key = key
  data[h].val = val

proc iiTablePut(t: var TIITable, key, val: int) =
  var index = iiTableRawGet(t, key)
  if index >= 0:
    assert(t.data[index].key != InvalidKey)
    t.data[index].val = val
  else:
    if mustRehash(len(t.data), t.counter):
      var n: TIIPairSeq
      newSeq(n, len(t.data) * GrowthFactor)
      for i in countup(0, high(n)): n[i].key = InvalidKey
      for i in countup(0, high(t.data)):
        if t.data[i].key != InvalidKey:
          iiTableRawInsert(n, t.data[i].key, t.data[i].val)
      swap(t.data, n)
    iiTableRawInsert(t.data, key, val)
    inc(t.counter)
