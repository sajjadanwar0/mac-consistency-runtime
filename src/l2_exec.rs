#![allow(unused_imports)]
#![allow(dead_code)]
//@ reinclude-textual: lib_l2_safety.rs
use vstd::prelude::*;
use vstd::hash_map::HashMapWithView;
use vstd::hash_set::HashSetWithView;

verus! {
pub type CellId  = int;
pub type TxnId   = int;
pub type Value   = int;
pub type Time    = int;

pub struct TxnState {
    pub started:       bool,
    pub committed:     bool,
    pub aborted:       bool,
    pub read_set:      Set<CellId>,
    pub read_values:   Map<CellId, Value>,
    pub write_set:     Set<CellId>,
    pub write_values:  Map<CellId, Value>,
    pub predecessors:  Set<TxnId>,
    pub read_from:     Map<CellId, TxnId>,
    pub read_at:       Map<CellId, Time>,
    pub commit_time:   Time,
}

pub open spec fn empty_txn() -> TxnState {
    TxnState {
        started:       false,
        committed:     false,
        aborted:       false,
        read_set:      Set::empty(),
        read_values:   Map::empty(),
        write_set:     Set::empty(),
        write_values:  Map::empty(),
        predecessors:  Set::empty(),
        read_from:     Map::empty(),
        read_at:       Map::empty(),
        commit_time:   0,
    }
}

pub struct RuntimeState {
    pub now:           Time,
    pub txns:          Map<TxnId, TxnState>,
    pub cell_value:    Map<CellId, Value>,
    pub cell_writer:   Map<CellId, TxnId>,
    pub all_txns:      Set<TxnId>,
}

pub open spec fn initial_state() -> RuntimeState {
    RuntimeState {
        now:           0,
        txns:          Map::empty(),
        cell_value:    Map::empty(),
        cell_writer:   Map::empty(),
        all_txns:      Set::empty(),
    }
}

pub open spec fn reads_fresh(s: RuntimeState, t: TxnId) -> bool {
    let txn = s.txns[t];
    forall |c: CellId| #![trigger txn.read_set.contains(c)]
        txn.read_set.contains(c)
        ==> s.cell_value.contains_key(c)
            && s.cell_value[c] == txn.read_values[c]
}

pub open spec fn predecessors_clean(s: RuntimeState, t: TxnId) -> bool {
    let txn = s.txns[t];
    forall |p: TxnId| #![trigger txn.predecessors.contains(p)]
        txn.predecessors.contains(p)
        ==> s.txns.contains_key(p)
            && s.txns[p].committed
            && !s.txns[p].aborted
}

pub open spec fn commit_valid(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].started
    && !s.txns[t].committed
    && !s.txns[t].aborted
    && reads_fresh(s, t)
    && predecessors_clean(s, t)
}

pub open spec fn pred_closed(s: RuntimeState) -> bool {
    forall |u: TxnId, p: TxnId, q: TxnId|
        #![trigger s.txns[u].predecessors.contains(p), s.txns[p].predecessors.contains(q)]
        s.txns.contains_key(u)
        && s.txns[u].predecessors.contains(p)
        && s.txns[p].predecessors.contains(q)
        ==> s.txns[u].predecessors.contains(q)
}

pub open spec fn invariant_committed_predecessors_clean(s: RuntimeState) -> bool {
    forall |t: TxnId| #![trigger s.txns[t].committed]
        s.txns.contains_key(t)
        && s.txns[t].committed
        && !s.txns[t].aborted
        ==> predecessors_clean(s, t)
}

pub open spec fn step_begin(s: RuntimeState, t: TxnId) -> RuntimeState {
    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, TxnState {
            started: true,
            ..empty_txn()
        }),
        all_txns: s.all_txns.insert(t),
        ..s
    }
}

pub open spec fn step_read(s: RuntimeState, t: TxnId, c: CellId) -> RuntimeState
    recommends
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        s.txns.contains_key(s.cell_writer[c]),
{
    let txn = s.txns[t];
    let writer = s.cell_writer[c];
    let new_txn = TxnState {
        read_set: txn.read_set.insert(c),
        read_values: txn.read_values.insert(c, s.cell_value[c]),
        predecessors: txn.predecessors.insert(writer).union(s.txns[writer].predecessors),
        read_from: txn.read_from.insert(c, writer),
        read_at: txn.read_at.insert(c, s.now),
        ..txn
    };
    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        ..s
    }
}

pub open spec fn step_write(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    -> RuntimeState
    recommends s.txns.contains_key(t)
{
    let txn = s.txns[t];
    let new_txn = TxnState {
        write_set: txn.write_set.insert(c),
        write_values: txn.write_values.insert(c, v),
        ..txn
    };
    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        ..s
    }
}

pub open spec fn step_commit(s: RuntimeState, t: TxnId) -> RuntimeState
    recommends commit_valid(s, t)
{
    let txn = s.txns[t];
    let new_txn = TxnState {
        committed: true,
        commit_time: s.now,
        ..txn
    };

    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        cell_value: publish_writes(s.cell_value, txn.write_set,
                                    txn.write_values),
        cell_writer: publish_writer(s.cell_writer, txn.write_set, t),
        ..s
    }
}

pub open spec fn publish_writes(
    cv: Map<CellId, Value>,
    ws: Set<CellId>,
    wv: Map<CellId, Value>,
) -> Map<CellId, Value> {
    Map::new(
        |c: CellId| ws.contains(c) || cv.contains_key(c),
        |c: CellId| if ws.contains(c) { wv[c] } else { cv[c] },
    )
}

pub open spec fn publish_writer(
    cw: Map<CellId, TxnId>,
    ws: Set<CellId>,
    t: TxnId,
) -> Map<CellId, TxnId> {
    Map::new(
        |c: CellId| ws.contains(c) || cw.contains_key(c),
        |c: CellId| if ws.contains(c) { t } else { cw[c] },
    )
}

pub open spec fn step_abort(s: RuntimeState, t: TxnId) -> RuntimeState {
    let txn = s.txns[t];
    let new_txn = TxnState { aborted: true, ..txn };
    let new_txns = cascade_abort(s.txns.insert(t, new_txn), t);
    RuntimeState {
        now: s.now + 1,
        txns: new_txns,
        ..s
    }
}

pub open spec fn cascade_abort(
    txns: Map<TxnId, TxnState>,
    t: TxnId,
) -> Map<TxnId, TxnState> {
    Map::new(
        |id: TxnId| txns.contains_key(id),
        |id: TxnId| {
            let txn = txns[id];
            if txn.predecessors.contains(t) {
                TxnState { aborted: true, ..txn }
            } else {
                txn
            }
        },
    )
}

pub open spec fn a1_witness_at_commit(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].committed
    && exists |c: CellId|
        #![trigger s.txns[t].read_set.contains(c)]
        s.txns[t].read_set.contains(c)
        && s.cell_value.contains_key(c)
        && s.cell_value[c] != s.txns[t].read_values[c]
}

pub open spec fn a3_witness(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].committed
    && !s.txns[t].aborted
    && exists |p: TxnId|
        #![trigger s.txns[t].predecessors.contains(p)]
        s.txns[t].predecessors.contains(p)
        && s.txns.contains_key(p)
        && s.txns[p].aborted
}

pub proof fn lemma_l2_no_a1_at_commit(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |c: CellId|
            s.txns[t].read_set.contains(c)
            && !s.txns[t].write_set.contains(c)
            ==> s.cell_value.contains_key(c)
                && s.cell_value[c] == s.txns[t].read_values[c],
{ }

pub proof fn lemma_l2_no_a3_at_commit(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |p: TxnId|
            s.txns[t].predecessors.contains(p)
            ==> s.txns.contains_key(p)
                && s.txns[p].committed
                && !s.txns[p].aborted,
{ }

pub proof fn lemma_cascade_preserves_clean_predecessors(
    s: RuntimeState, t: TxnId,
)
    requires
        invariant_committed_predecessors_clean(s),
        pred_closed(s),
        s.txns.contains_key(t),
    ensures
        invariant_committed_predecessors_clean(step_abort(s, t)),
{
    let s2 = step_abort(s, t);
    assert forall |u: TxnId|
        s2.txns.contains_key(u)
        && s2.txns[u].committed
        && !s2.txns[u].aborted
        implies predecessors_clean(s2, u)
    by {
        let u_txn = s2.txns[u];
        assert(!u_txn.aborted);
        assert(!s.txns[u].predecessors.contains(t));
        assert(u_txn.predecessors == s.txns[u].predecessors);
        assert(predecessors_clean(s, u));
        assert forall |p: TxnId|
            u_txn.predecessors.contains(p)
            implies s2.txns.contains_key(p)
                && s2.txns[p].committed
                && !s2.txns[p].aborted
        by {
            assert(!s.txns[u].predecessors.contains(t));

            if s.txns[p].predecessors.contains(t) {
                assert(s.txns[u].predecessors.contains(t));
                assert(false);
            }

            assert(!s.txns[p].predecessors.contains(t));
            assert(p != t);
            assert(s.txns.contains_key(p));
            assert(s.txns[p].committed);
            assert(!s.txns[p].aborted);
            assert(s2.txns.contains_key(p));
            assert(s2.txns[p].committed);
            assert(!s2.txns[p].aborted);
        }
    }
}

pub proof fn lemma_commit_valid_implies_no_a1(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |c: CellId|
            #![trigger s.txns[t].read_set.contains(c)]
            s.txns[t].read_set.contains(c)
            && !s.txns[t].write_set.contains(c)
            ==> s.cell_value[c] == s.txns[t].read_values[c],
{ }

pub proof fn lemma_commit_valid_implies_no_a3(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures !a3_witness(step_commit(s, t), t)
        || forall |p: TxnId|
            s.txns[t].predecessors.contains(p)
            ==> !s.txns[p].aborted,
{ }

pub proof fn lemma_no_cascade_admits_a3(s: RuntimeState, t: TxnId, p: TxnId)
    requires
        s.txns.contains_key(t),
        s.txns[t].committed,
        !s.txns[t].aborted,
        s.txns[t].predecessors.contains(p),
        s.txns.contains_key(p),
        s.txns[p].aborted,
    ensures a3_witness(s, t),
{
    assert(s.txns[t].predecessors.contains(p)
        && s.txns.contains_key(p)
        && s.txns[p].aborted);
}

pub open spec fn inv_writers_committed(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_writer[c]]
        s.cell_value.contains_key(c)
        ==> s.txns.contains_key(s.cell_writer[c])
            && s.txns[s.cell_writer[c]].committed
}

pub open spec fn inv_cell_domains(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_value.contains_key(c)]
        s.cell_value.contains_key(c) <==> s.cell_writer.contains_key(c)
}

pub open spec fn inv_cell_writer_wrote(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_writer[c]]
        s.cell_value.contains_key(c)
        ==> s.txns.contains_key(s.cell_writer[c])
            && s.txns[s.cell_writer[c]].write_set.contains(c)
            && s.txns[s.cell_writer[c]].write_values[c] == s.cell_value[c]
}

pub open spec fn inv_read_provenance(s: RuntimeState) -> bool {
    forall |tt: TxnId, cc: CellId| #![trigger s.txns[tt].read_set.contains(cc)]
        (s.txns.contains_key(tt) && s.txns[tt].read_set.contains(cc))
        ==> s.txns[tt].read_from.contains_key(cc)
            && s.txns[tt].predecessors.contains(s.txns[tt].read_from[cc])
            && s.txns.contains_key(s.txns[tt].read_from[cc])
            && s.txns[s.txns[tt].read_from[cc]].write_set.contains(cc)
            && s.txns[s.txns[tt].read_from[cc]].write_values[cc]
                 == s.txns[tt].read_values[cc]
}

pub open spec fn inv_committed_frozen(s: RuntimeState) -> bool {
    forall |u: TxnId, p: TxnId| #![trigger s.txns[u].predecessors.contains(p)]
        s.txns.contains_key(u) && s.txns[u].predecessors.contains(p)
        ==> s.txns.contains_key(p) && s.txns[p].committed
}

pub proof fn lemma_step_read_preserves_pred_closed(
    s: RuntimeState, t: TxnId, c: CellId,
)
    requires
        pred_closed(s),
        inv_writers_committed(s),
        inv_committed_frozen(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,
    ensures
        pred_closed(step_read(s, t, c)),
{
    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];
    let old = s.txns[t].predecessors;
    let wp = s.txns[writer].predecessors;
    assert(s2.txns[t].predecessors =~= old.insert(writer).union(wp));

    assert forall |u: TxnId, p: TxnId, q: TxnId|
        #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
        s2.txns.contains_key(u)
        && s2.txns[u].predecessors.contains(p)
        && s2.txns[p].predecessors.contains(q)
        implies s2.txns[u].predecessors.contains(q)
    by {
        if u == t {
            if p == t {
            } else {
                assert(s2.txns[p].predecessors =~= s.txns[p].predecessors);
                assert(s2.txns[t].predecessors.contains(p));
                if old.contains(p) {
                    assert(s.txns[t].predecessors.contains(p));
                    assert(s.txns[p].predecessors.contains(q));
                    assert(old.contains(q));
                } else if p == writer {
                    assert(s.txns[writer].predecessors.contains(q));
                    assert(wp.contains(q));
                } else {
                    assert(s.txns.contains_key(writer));
                    assert(wp.contains(p));
                    assert(s.txns[writer].predecessors.contains(p));
                    assert(s.txns[p].predecessors.contains(q));
                    assert(wp.contains(q));
                }
                assert(old.insert(writer).union(wp).contains(q));
                assert(s2.txns[u].predecessors.contains(q));
            }
        } else {
            assert(s2.txns[u].predecessors =~= s.txns[u].predecessors);

            if p == t {
                assert(s.txns[u].predecessors.contains(t));
                assert(s.txns[t].committed);
                assert(false);
            } else {
                assert(s2.txns[p].predecessors =~= s.txns[p].predecessors);
                assert(s.txns[u].predecessors.contains(p));
                assert(s.txns[p].predecessors.contains(q));
                assert(s.txns[u].predecessors.contains(q));
            }
        }
    }
}

pub open spec fn inv_l2(s: RuntimeState) -> bool {
    &&& invariant_committed_predecessors_clean(s)
    &&& pred_closed(s)
    &&& inv_writers_committed(s)
    &&& inv_committed_frozen(s)
    &&& inv_cell_domains(s)
    &&& inv_cell_writer_wrote(s)
    &&& inv_read_provenance(s)
}

pub open spec fn inv_commit_time_le_now(s: RuntimeState) -> bool {
    forall |t: TxnId| #![trigger s.txns[t].commit_time]
        (s.txns.contains_key(t) && s.txns[t].committed)
        ==> s.txns[t].commit_time <= s.now
}

pub open spec fn inv_read_temporal(s: RuntimeState) -> bool {
    forall |tt: TxnId, cc: CellId| #![trigger s.txns[tt].read_set.contains(cc)]
        (s.txns.contains_key(tt) && s.txns[tt].read_set.contains(cc))
        ==> s.txns.contains_key(s.txns[tt].read_from[cc])
            && s.txns[s.txns[tt].read_from[cc]].commit_time
                 <= s.txns[tt].read_at[cc]
}

pub open spec fn inv_l2t(s: RuntimeState) -> bool {
    &&& inv_l2(s)
    &&& inv_commit_time_le_now(s)
    &&& inv_read_temporal(s)
}

pub proof fn lemma_begin_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), !s.txns.contains_key(t),
    ensures inv_l2(step_begin(s, t)),
{
    let s2 = step_begin(s, t);
    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            assert(s2.cell_value[c] == s.cell_value[c]);
            assert(s2.cell_writer[c] == s.cell_writer[c]);
            let w = s.cell_writer[c];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(c));
            assert(s.txns[w].write_values[c] == s.cell_value[c]);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set =~= Set::<CellId>::empty());
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                let w = s.txns[tt].read_from[cc];
                assert(s.txns[tt].read_set.contains(cc));
                assert(s.txns[tt].predecessors.contains(w));
                assert(s.txns.contains_key(w));
                assert(s.txns[w].write_set.contains(cc));
                assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }
}

pub proof fn lemma_write_preserves_inv_l2(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    requires inv_l2(s), s.txns.contains_key(t), !s.txns[t].committed,
    ensures inv_l2(step_write(s, t, c, v)),
{
    let s2 = step_write(s, t, c, v);

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |cc: CellId| #![trigger s2.cell_writer[cc]]
            s2.cell_value.contains_key(cc) implies
                s2.txns.contains_key(s2.cell_writer[cc])
                && s2.txns[s2.cell_writer[cc]].write_set.contains(cc)
                && s2.txns[s2.cell_writer[cc]].write_values[cc] == s2.cell_value[cc]
        by {
            assert(s2.cell_value[cc] == s.cell_value[cc]);
            assert(s2.cell_writer[cc] == s.cell_writer[cc]);
            let w = s.cell_writer[cc];
            assert(s.txns.contains_key(w) && s.txns[w].committed);
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.cell_value[cc]);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);
                assert(s2.txns[t].read_values == s.txns[t].read_values);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].predecessors == s.txns[t].predecessors);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }
            let w = s.txns[tt].read_from[cc];
            assert(s.txns[tt].read_set.contains(cc));
            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
            assert(s.txns[w].committed);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }
}

pub proof fn lemma_abort_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), s.txns.contains_key(t),
    ensures inv_l2(step_abort(s, t)),
{
    lemma_cascade_preserves_clean_predecessors(s, t);
    let s2 = step_abort(s, t);

    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].predecessors == s.txns[x].predecessors
            && s2.txns[x].committed == s.txns[x].committed
            && s2.txns[x].write_set == s.txns[x].write_set
            && s2.txns[x].write_values == s.txns[x].write_values
            && s2.txns[x].read_set == s.txns[x].read_set
            && s2.txns[x].read_values == s.txns[x].read_values
            && s2.txns[x].read_from == s.txns[x].read_from
    by {
        let base = s.txns.insert(t, TxnState { aborted: true, ..s.txns[t] });

        assert(base.contains_key(x));
        assert(base[x].predecessors == s.txns[x].predecessors);
        assert(base[x].committed == s.txns[x].committed);
        assert(base[x].write_set == s.txns[x].write_set);
        assert(base[x].write_values == s.txns[x].write_values);
        assert(base[x].read_set == s.txns[x].read_set);
        assert(base[x].read_values == s.txns[x].read_values);
        assert(base[x].read_from == s.txns[x].read_from);
        assert(s2.txns[x].predecessors == base[x].predecessors);
        assert(s2.txns[x].committed == base[x].committed);
        assert(s2.txns[x].write_set == base[x].write_set);
        assert(s2.txns[x].write_values == base[x].write_values);
        assert(s2.txns[x].read_set == base[x].read_set);
        assert(s2.txns[x].read_values == base[x].read_values);
        assert(s2.txns[x].read_from == base[x].read_from);
    }

    assert(s2.cell_value =~= s.cell_value);
    assert(s2.cell_writer =~= s.cell_writer);

    assert(pred_closed(s2)) by {
        assert forall |u: TxnId, p: TxnId, q: TxnId|
            #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            && s2.txns[p].predecessors.contains(q)
            implies s2.txns[u].predecessors.contains(q)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].predecessors == s.txns[p].predecessors);
        }
    }

    assert(inv_committed_frozen(s2)) by {
        assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            implies s2.txns.contains_key(p) && s2.txns[p].committed
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].committed == s.txns[p].committed);
        }
    }

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            assert(s2.cell_value[c] == s.cell_value[c]);
            assert(s2.cell_writer[c] == s.cell_writer[c]);
            let w = s.cell_writer[c];
            assert(s.cell_value.contains_key(c));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(c));
            assert(s.txns[w].write_values[c] == s.cell_value[c]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].write_set == s.txns[w].write_set);
            assert(s2.txns[w].write_values == s.txns[w].write_values);
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            assert(s2.txns[tt].read_set == s.txns[tt].read_set);
            assert(s2.txns[tt].read_values == s.txns[tt].read_values);
            assert(s2.txns[tt].read_from == s.txns[tt].read_from);
            assert(s2.txns[tt].predecessors == s.txns[tt].predecessors);
            let w = s.txns[tt].read_from[cc];
            assert(s.txns[tt].read_set.contains(cc));
            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].write_set == s.txns[w].write_set);
            assert(s2.txns[w].write_values == s.txns[w].write_values);
        }
    }
}

pub proof fn lemma_read_preserves_inv_l2(s: RuntimeState, t: TxnId, c: CellId)
    requires
        inv_l2(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,
    ensures inv_l2(step_read(s, t, c)),
{
    lemma_step_read_preserves_pred_closed(s, t, c);
    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];

    assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
        s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
        implies s2.txns.contains_key(p) && s2.txns[p].committed
    by {
        if u == t {
         if s.txns[t].predecessors.contains(p) {
            } else if p == writer {
            } else {
                assert(s.txns[writer].predecessors.contains(p));
            }
        }
    }

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |cc: CellId| #![trigger s2.cell_writer[cc]]
            s2.cell_value.contains_key(cc) implies
                s2.txns.contains_key(s2.cell_writer[cc])
                && s2.txns[s2.cell_writer[cc]].write_set.contains(cc)
                && s2.txns[s2.cell_writer[cc]].write_values[cc] == s2.cell_value[cc]
        by {
            assert(s2.cell_value[cc] == s.cell_value[cc]);
            assert(s2.cell_writer[cc] == s.cell_writer[cc]);
            let w = s.cell_writer[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.cell_value[cc]);
            if w == t {
                assert(s2.txns[t].write_set == s.txns[t].write_set);
                assert(s2.txns[t].write_values == s.txns[t].write_values);
            } else {
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }

    assert(inv_read_provenance(s2)) by {
        let writer = s.cell_writer[c];
        assert(s2.txns[t].predecessors =~=
               s.txns[t].predecessors.insert(writer).union(s.txns[writer].predecessors));
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                if cc == c {
                    assert(s2.txns[t].read_from[c] == writer);
                    assert(s2.txns[t].read_from.contains_key(c));
                    assert(s2.txns[t].predecessors.contains(writer));
                    assert(s2.txns[t].read_values[c] == s.cell_value[c]);
                    assert(s.cell_value.contains_key(c));
                    assert(s.txns.contains_key(writer) && s.txns[writer].committed);
                    assert(writer != t);
                    assert(s2.txns[writer] == s.txns[writer]);
                    assert(s.txns[writer].write_set.contains(c));
                    assert(s.txns[writer].write_values[c] == s.cell_value[c]);
                } else {
                    assert(s.txns[t].read_set.contains(cc));

                    let w = s.txns[t].read_from[cc];

                    assert(s.txns[t].read_from.contains_key(cc));
                    assert(s.txns[t].predecessors.contains(w));
                    assert(s.txns.contains_key(w));
                    assert(s.txns[w].write_set.contains(cc));
                    assert(s.txns[w].write_values[cc] == s.txns[t].read_values[cc]);
                    assert(s2.txns[t].read_from[cc] == w);
                    assert(s2.txns[t].read_from.contains_key(cc));
                    assert(s2.txns[t].predecessors.contains(w));
                    assert(s2.txns[t].read_values[cc] == s.txns[t].read_values[cc]);
                    assert(s.txns[w].committed);
                    assert(w != t);
                    assert(s2.txns[w] == s.txns[w]);
                }
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                let w = s.txns[tt].read_from[cc];
                assert(s.txns[tt].read_set.contains(cc));
                assert(s.txns[tt].predecessors.contains(w));
                assert(s.txns.contains_key(w));
                assert(s.txns[w].write_set.contains(cc));
                assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
                assert(s.txns[w].committed);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }
}

pub proof fn lemma_commit_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), commit_valid(s, t),
    ensures inv_l2(step_commit(s, t)),
{
    let s2 = step_commit(s, t);
    let ws = s.txns[t].write_set;

    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].predecessors == s.txns[x].predecessors
            && (s2.txns[x].aborted == s.txns[x].aborted)
    by { }

    assert(inv_cell_domains(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_value.contains_key(c)]
            s2.cell_value.contains_key(c) <==> s2.cell_writer.contains_key(c)
        by {
        }
    }

    assert forall |c: CellId| #![trigger s2.cell_writer[c]]
        s2.cell_value.contains_key(c)
        implies s2.txns.contains_key(s2.cell_writer[c])
            && s2.txns[s2.cell_writer[c]].committed
    by {
        if ws.contains(c) {
            assert(s2.cell_writer[c] == t);
            assert(s2.txns[t].committed);
        } else {
            assert(s2.cell_value.contains_key(c));
            assert(s.cell_value.contains_key(c));
            assert(s.cell_writer.contains_key(c));
            assert(s2.cell_writer[c] == s.cell_writer[c]);
        }
    }

    assert(invariant_committed_predecessors_clean(s2)) by {
        assert forall |u: TxnId| #![trigger s2.txns[u].committed]
            s2.txns.contains_key(u) && s2.txns[u].committed && !s2.txns[u].aborted
            implies predecessors_clean(s2, u)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);

            if u != t {
                assert(s.txns[u].committed);
            }
            assert forall |p: TxnId| s.txns[u].predecessors.contains(p)
                implies s2.txns.contains_key(p)
                    && s2.txns[p].committed && !s2.txns[p].aborted
            by {
                assert(s.txns.contains_key(p) && s.txns[p].committed && !s.txns[p].aborted);
                assert(p != t);
                assert(s2.txns[p] == s.txns[p]);
            }
        }
    }

    assert(pred_closed(s2)) by {
        assert forall |u: TxnId, p: TxnId, q: TxnId|
            #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            && s2.txns[p].predecessors.contains(q)
            implies s2.txns[u].predecessors.contains(q)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].predecessors == s.txns[p].predecessors);
        }
    }
    assert(inv_committed_frozen(s2)) by {
        assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            implies s2.txns.contains_key(p) && s2.txns[p].committed
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
        }
    }

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            if ws.contains(c) {
                assert(s2.cell_writer[c] == t);
                assert(s2.cell_value[c] == s.txns[t].write_values[c]);
                assert(s2.txns[t].write_set == s.txns[t].write_set);
                assert(s2.txns[t].write_set.contains(c));
                assert(s2.txns[t].write_values == s.txns[t].write_values);
            } else {
                assert(s.cell_value.contains_key(c));
                assert(s.cell_writer.contains_key(c));
                assert(s2.cell_writer[c] == s.cell_writer[c]);
                assert(s2.cell_value[c] == s.cell_value[c]);

                let w = s.cell_writer[c];

                assert(s.txns.contains_key(w) && s.txns[w].committed);
                assert(s.txns[w].write_set.contains(c));
                assert(s.txns[w].write_values[c] == s.cell_value[c]);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);          // ..txn
                assert(s2.txns[t].read_values == s.txns[t].read_values);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].predecessors == s.txns[t].predecessors);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }
            let w = s.txns[tt].read_from[cc];
            assert(s.txns[tt].read_set.contains(cc));
            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
            assert(s.txns[w].committed);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }
}

pub proof fn lemma_initial_inv_l2()
    ensures inv_l2(initial_state())
{
    assert(initial_state().txns =~= Map::<TxnId, TxnState>::empty());
    assert(initial_state().cell_value =~= Map::<CellId, Value>::empty());
    assert(initial_state().cell_writer =~= Map::<CellId, TxnId>::empty());
}

pub proof fn lemma_l2_reachable_no_a3(s: RuntimeState)
    requires inv_l2(s),
    ensures forall |t: TxnId| #![trigger s.txns[t].committed] !a3_witness(s, t),
{
    assert forall |t: TxnId| #![trigger s.txns[t].committed]
        !a3_witness(s, t)
    by {
        if a3_witness(s, t) {
            let p = choose |p: TxnId|
                s.txns[t].predecessors.contains(p)
                && s.txns.contains_key(p) && s.txns[p].aborted;
            assert(s.txns[t].predecessors.contains(p));
            assert(invariant_committed_predecessors_clean(s));
            assert(predecessors_clean(s, t));
            assert(s.txns[p].committed && !s.txns[p].aborted);
            assert(false);
        }
    }
}

pub proof fn lemma_l2_reads_supported(s: RuntimeState)
    requires inv_l2(s),
    ensures
        forall |t: TxnId, c: CellId|
            (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
             && s.txns[t].read_set.contains(c))
            ==> exists |w: TxnId|
                s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
                && s.txns[w].write_set.contains(c)
                && s.txns[w].write_values[c] == s.txns[t].read_values[c],
{
    assert forall |t: TxnId, c: CellId|
        (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
         && s.txns[t].read_set.contains(c)) implies
        exists |w: TxnId|
            s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]
    by {
        let w = s.txns[t].read_from[c];

        assert(s.txns[t].read_set.contains(c));
        assert(s.txns[t].predecessors.contains(w));
        assert(s.txns.contains_key(w));
        assert(s.txns[w].write_set.contains(c));
        assert(s.txns[w].write_values[c] == s.txns[t].read_values[c]);
        assert(invariant_committed_predecessors_clean(s));
        assert(predecessors_clean(s, t));
        assert(s.txns[w].committed && !s.txns[w].aborted);
        assert(s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]);
    }
}

pub proof fn lemma_begin_preserves_inv_l2t(s: RuntimeState, t: TxnId)
    requires inv_l2t(s), !s.txns.contains_key(t),
    ensures inv_l2t(step_begin(s, t)),
{
    lemma_begin_preserves_inv_l2(s, t);
    let s2 = step_begin(s, t);
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(!s2.txns[t].committed);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set =~= Set::<CellId>::empty());
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                assert(s.txns[tt].read_set.contains(cc));
                let w = s.txns[tt].read_from[cc];
                assert(s.txns.contains_key(w));
                assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
                assert(s2.txns[tt].read_from[cc] == w);
                assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
            }
        }
    }
}

pub proof fn lemma_write_preserves_inv_l2t(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    requires inv_l2t(s), s.txns.contains_key(t), !s.txns[t].committed,
    ensures inv_l2t(step_write(s, t, c, v)),
{
    lemma_write_preserves_inv_l2(s, t, c, v);
    let s2 = step_write(s, t, c, v);
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(s2.txns[t].committed == s.txns[t].committed);
                assert(!s.txns[t].committed);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].read_at == s.txns[t].read_at);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }
            assert(s.txns[tt].read_set.contains(cc));
            let w = s.txns[tt].read_from[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
            if w == t {
                assert(s2.txns[t].commit_time == s.txns[t].commit_time);
            } else {
                assert(s2.txns[w] == s.txns[w]);
            }
            assert(s2.txns[tt].read_from[cc] == w);
            assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
        }
    }
}

pub proof fn lemma_abort_preserves_inv_l2t(s: RuntimeState, t: TxnId)
    requires inv_l2t(s), s.txns.contains_key(t),
    ensures inv_l2t(step_abort(s, t)),
{
    lemma_abort_preserves_inv_l2(s, t);
    let s2 = step_abort(s, t);
    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].committed == s.txns[x].committed
            && s2.txns[x].commit_time == s.txns[x].commit_time
            && s2.txns[x].read_set == s.txns[x].read_set
            && s2.txns[x].read_from == s.txns[x].read_from
            && s2.txns[x].read_at == s.txns[x].read_at
    by {
        let base = s.txns.insert(t, TxnState { aborted: true, ..s.txns[t] });
        assert(base.contains_key(x));
        assert(base[x].committed == s.txns[x].committed);
        assert(base[x].commit_time == s.txns[x].commit_time);
        assert(base[x].read_set == s.txns[x].read_set);
        assert(base[x].read_from == s.txns[x].read_from);
        assert(base[x].read_at == s.txns[x].read_at);
        assert(s2.txns[x].committed == base[x].committed);
        assert(s2.txns[x].commit_time == base[x].commit_time);
        assert(s2.txns[x].read_set == base[x].read_set);
        assert(s2.txns[x].read_from == base[x].read_from);
        assert(s2.txns[x].read_at == base[x].read_at);
    }
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            assert(s2.txns[x].committed == s.txns[x].committed);
            assert(s2.txns[x].commit_time == s.txns[x].commit_time);
            assert(s.txns[x].commit_time <= s.now);
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            assert(s2.txns[tt].read_set == s.txns[tt].read_set);
            assert(s2.txns[tt].read_from == s.txns[tt].read_from);
            assert(s2.txns[tt].read_at == s.txns[tt].read_at);
            assert(s.txns[tt].read_set.contains(cc));
            let w = s.txns[tt].read_from[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].commit_time == s.txns[w].commit_time);
        }
    }
}

pub proof fn lemma_read_preserves_inv_l2t(s: RuntimeState, t: TxnId, c: CellId)
    requires
        inv_l2t(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,
    ensures inv_l2t(step_read(s, t, c)),
{
    lemma_read_preserves_inv_l2(s, t, c);
    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(s2.txns[t].committed == s.txns[t].committed);
                assert(!s.txns[t].committed);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                if cc == c {
                    assert(s2.txns[t].read_from[c] == writer);
                    assert(s2.txns[t].read_at[c] == s.now);
                    assert(s.txns.contains_key(writer) && s.txns[writer].committed);
                    assert(s.txns[writer].commit_time <= s.now);
                    assert(writer != t);
                    assert(s2.txns[writer] == s.txns[writer]);
                } else {
                    assert(s.txns[t].read_set.contains(cc));
                    assert(s.txns[t].predecessors.contains(s.txns[t].read_from[cc]));

                    let w = s.txns[t].read_from[cc];

                    assert(s.txns.contains_key(w));
                    assert(s.txns[w].committed);
                    assert(w != t);
                    assert(s.txns[w].commit_time <= s.txns[t].read_at[cc]);
                    assert(s2.txns[t].read_from[cc] == w);
                    assert(s2.txns[t].read_at[cc] == s.txns[t].read_at[cc]);
                    assert(s2.txns[w] == s.txns[w]);
                }
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                assert(s.txns[tt].read_set.contains(cc));
                assert(s.txns[tt].predecessors.contains(s.txns[tt].read_from[cc]));
                let w = s.txns[tt].read_from[cc];
                assert(s.txns.contains_key(w));
                assert(s.txns[w].committed);
                assert(w != t);
                assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
                assert(s2.txns[w] == s.txns[w]);
                assert(s2.txns[tt].read_from[cc] == w);
                assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
            }
        }
    }
}

pub proof fn lemma_commit_preserves_inv_l2t(s: RuntimeState, t: TxnId)
    requires inv_l2t(s), commit_valid(s, t),
    ensures inv_l2t(step_commit(s, t)),
{
    lemma_commit_preserves_inv_l2(s, t);
    let s2 = step_commit(s, t);
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(s2.txns[t].commit_time == s.now);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].read_at == s.txns[t].read_at);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }

            assert(s.txns[tt].read_set.contains(cc));

            let w = s.txns[tt].read_from[cc];

            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].committed);
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
            assert(s2.txns[tt].read_from[cc] == w);
            assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
        }
    }
}

pub proof fn lemma_initial_inv_l2t()
    ensures inv_l2t(initial_state())
{
    lemma_initial_inv_l2();
    assert(initial_state().txns =~= Map::<TxnId, TxnState>::empty());
}

pub proof fn lemma_l2_reads_supported_temporal(s: RuntimeState)
    requires inv_l2t(s),
    ensures
        forall |t: TxnId, c: CellId|
            (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
             && s.txns[t].read_set.contains(c))
            ==> exists |w: TxnId|
                s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
                && s.txns[w].write_set.contains(c)
                && s.txns[w].write_values[c] == s.txns[t].read_values[c]
                && s.txns[w].commit_time <= s.txns[t].read_at[c],
{
    lemma_l2_reads_supported(s);
    assert forall |t: TxnId, c: CellId|
        (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
         && s.txns[t].read_set.contains(c)) implies
        exists |w: TxnId|
            s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]
            && s.txns[w].commit_time <= s.txns[t].read_at[c]
    by {
        let w = s.txns[t].read_from[c];

        assert(s.txns[t].predecessors.contains(w));
        assert(s.txns.contains_key(w));
        assert(s.txns[w].write_set.contains(c));
        assert(s.txns[w].write_values[c] == s.txns[t].read_values[c]);
        assert(invariant_committed_predecessors_clean(s));
        assert(predecessors_clean(s, t));
        assert(s.txns[w].committed && !s.txns[w].aborted);
        assert(s.txns[w].commit_time <= s.txns[t].read_at[c]);
        assert(s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]
            && s.txns[w].commit_time <= s.txns[t].read_at[c]);
    }
}

pub open spec fn in_u64(c: int) -> bool { 0 <= c <= u64::MAX as int }

pub proof fn lemma_u64_roundtrip(k: u64)
    ensures (k as int) as u64 == k, in_u64(k as int),
{}

pub proof fn lemma_int_roundtrip(c: int)
    requires in_u64(c),
    ensures (c as u64) as int == c,
{}

pub open spec fn view_u64_set(s: Set<u64>) -> Set<int> {
    Set::new(|c: int| in_u64(c) && s.contains(c as u64))
}
pub open spec fn view_u64_map(m: Map<u64, u64>) -> Map<int, int> {
    Map::new(
        |c: int| in_u64(c) && m.contains_key(c as u64),
        |c: int| m[c as u64] as int,
    )
}

pub open spec fn view_vec_u64_set(s: Seq<u64>) -> Set<int> {
    Set::new(|x: int| exists |i: int| 0 <= i < s.len() && s[i] as int == x)
}

pub proof fn lemma_vec_set_empty()
    ensures view_vec_u64_set(Seq::<u64>::empty()) =~= Set::<int>::empty(),
{
    assert forall |x: int| !view_vec_u64_set(Seq::<u64>::empty()).contains(x) by {
        assert(Seq::<u64>::empty().len() == 0);
    }
}

pub proof fn lemma_vec_set_push(s: Seq<u64>, x: u64)
    ensures view_vec_u64_set(s.push(x)) =~= view_vec_u64_set(s).insert(x as int),
{
    let sp = s.push(x);
    lemma_u64_roundtrip(x);
    assert forall |y: int|
        view_vec_u64_set(sp).contains(y) <==> view_vec_u64_set(s).insert(x as int).contains(y)
    by {
        if view_vec_u64_set(sp).contains(y) {
            let i = choose |i: int| 0 <= i < sp.len() && sp[i] as int == y;
            if i < s.len() {
                assert(sp[i] == s[i]);
            } else {
                assert(i == s.len());
                assert(sp[i] == x);
            }
        }
        if view_vec_u64_set(s).insert(x as int).contains(y) {
            if y == x as int {
                assert(sp[s.len() as int] == x);
                assert(0 <= s.len() < sp.len());
            } else {
                let i = choose |i: int| 0 <= i < s.len() && s[i] as int == y;
                assert(sp[i] == s[i]);
            }
        }
    }
}

pub proof fn lemma_vec_set_contains_iff(s: Seq<u64>, x: u64)
    ensures view_vec_u64_set(s).contains(x as int)
            <==> (exists |i: int| 0 <= i < s.len() && s[i] == x),
{
    lemma_u64_roundtrip(x);
    if view_vec_u64_set(s).contains(x as int) {
        let i = choose |i: int| 0 <= i < s.len() && s[i] as int == (x as int);
        assert(s[i] == x);
    }
    if exists |i: int| 0 <= i < s.len() && s[i] == x {
        let i = choose |i: int| 0 <= i < s.len() && s[i] == x;
        assert(s[i] as int == x as int);
    }
}

pub struct ExecTxn {
    pub started:      bool,
    pub committed:    bool,
    pub aborted:      bool,
    pub read_set:     HashSetWithView<u64>,
    pub read_values:  HashMapWithView<u64, u64>,
    pub writes:       Vec<(u64, u64)>,
    pub predecessors: Vec<u64>,
    pub read_from:    HashMapWithView<u64, u64>,
    pub read_at:      HashMapWithView<u64, u64>,
    pub commit_time:  u64,
}

impl ExecTxn {
    pub open spec fn view(self) -> TxnState {
        TxnState {
            started:      self.started,
            committed:    self.committed,
            aborted:      self.aborted,
            read_set:     view_u64_set(self.read_set@),
            read_values:  view_u64_map(self.read_values@),
            write_set:    writes_set(self.writes@),
            write_values: writes_map(self.writes@),
            predecessors: view_vec_u64_set(self.predecessors@),
            read_from:    view_u64_map(self.read_from@),
            read_at:      view_u64_map(self.read_at@),
            commit_time:  self.commit_time as int,
        }
    }

    pub fn new_started() -> (r: ExecTxn)
        ensures r.view() == (TxnState { started: true, ..empty_txn() }),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let r = ExecTxn {
            started: true, committed: false, aborted: false,
            read_set:     HashSetWithView::new(),
            read_values:  HashMapWithView::new(),
            writes:       Vec::new(),
            predecessors: Vec::new(),
            read_from:    HashMapWithView::new(),
            read_at:      HashMapWithView::new(),
            commit_time:  0,
        };
        proof {
            assert(view_u64_set(r.read_set@) =~= Set::<int>::empty());
            assert(writes_set(r.writes@) =~= Set::<int>::empty());
            assert(view_vec_u64_set(r.predecessors@) =~= Set::<int>::empty());
            assert(view_u64_map(r.read_values@) =~= Map::<int, int>::empty());
            assert(writes_map(r.writes@) =~= Map::<int, int>::empty());
            assert(view_u64_map(r.read_from@) =~= Map::<int, int>::empty());
            assert(view_u64_map(r.read_at@) =~= Map::<int, int>::empty());
            assert(r.view() =~= (TxnState { started: true, ..empty_txn() }));
        }
        r
    }
}

pub open spec fn view_txns_map(m: Map<u64, ExecTxn>) -> Map<int, TxnState> {
    Map::new(
        |t: int| in_u64(t) && m.contains_key(t as u64),
        |t: int| m[t as u64].view(),
    )
}
pub open spec fn view_alltxns(m: Map<u64, ExecTxn>) -> Set<int> {
    Set::new(|t: int| in_u64(t) && m.contains_key(t as u64))
}

pub proof fn lemma_view_txns_insert(m: Map<u64, ExecTxn>, k: u64, v: ExecTxn)
    ensures
        view_txns_map(m.insert(k, v)) =~= view_txns_map(m).insert(k as int, v.view()),
        view_alltxns(m.insert(k, v)) =~= view_alltxns(m).insert(k as int),
{
    lemma_u64_roundtrip(k);
    assert forall |t: int| #[trigger] in_u64(t) implies (t as u64) as int == t by {
        lemma_int_roundtrip(t);
    }
    assert(view_txns_map(m.insert(k, v)) =~= view_txns_map(m).insert(k as int, v.view()));
    assert(view_alltxns(m.insert(k, v)) =~= view_alltxns(m).insert(k as int));
}

pub proof fn lemma_view_set_insert(s: Set<u64>, c: u64)
    ensures view_u64_set(s.insert(c)) =~= view_u64_set(s).insert(c as int),
{
    lemma_u64_roundtrip(c);
    assert forall |x: int| #[trigger] in_u64(x) implies (x as u64) as int == x by {
        lemma_int_roundtrip(x);
    }
    assert(view_u64_set(s.insert(c)) =~= view_u64_set(s).insert(c as int));
}

pub proof fn lemma_view_map_insert(m: Map<u64, u64>, c: u64, v: u64)
    ensures view_u64_map(m.insert(c, v)) =~= view_u64_map(m).insert(c as int, v as int),
{
    lemma_u64_roundtrip(c);
    assert forall |x: int| #[trigger] in_u64(x) implies (x as u64) as int == x by {
        lemma_int_roundtrip(x);
    }
    assert(view_u64_map(m.insert(c, v)) =~= view_u64_map(m).insert(c as int, v as int));
}

pub open spec fn last_val(s: Seq<(u64, u64)>, c: u64) -> u64
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else if s[s.len() - 1].0 == c { s[s.len() - 1].1 }
    else { last_val(s.drop_last(), c) }
}

pub open spec fn writes_set(s: Seq<(u64, u64)>) -> Set<int> {
    Set::new(|c: int| in_u64(c) && exists |i: int| 0 <= i < s.len() && #[trigger] s[i].0 == c as u64)
}

pub open spec fn writes_map(s: Seq<(u64, u64)>) -> Map<int, int> {
    Map::new(
        |c: int| in_u64(c) && exists |i: int| 0 <= i < s.len() && #[trigger] s[i].0 == c as u64,
        |c: int| last_val(s, c as u64) as int,
    )
}

pub proof fn lemma_last_val_push(s: Seq<(u64, u64)>, c: u64, v: u64, x: u64)
    ensures last_val(s.push((c, v)), x) == if x == c { v } else { last_val(s, x) },
{
    let sp = s.push((c, v));
    assert(sp.len() == s.len() + 1);
    assert(sp[sp.len() - 1] == (c, v));
    assert(sp.drop_last() =~= s);
}

pub proof fn lemma_writes_push(s: Seq<(u64, u64)>, c: u64, v: u64)
    ensures
        writes_set(s.push((c, v))) =~= writes_set(s).insert(c as int),
        writes_map(s.push((c, v))) =~= writes_map(s).insert(c as int, v as int),
{
    lemma_u64_roundtrip(c);
    assert forall |x: int| #[trigger] in_u64(x) implies (x as u64) as int == x by {
        lemma_int_roundtrip(x);
    }
    let sp = s.push((c, v));
    assert(sp.len() == s.len() + 1);
    assert(sp[sp.len() - 1] == (c, v));
    assert forall |x: u64| #[trigger] last_val(sp, x)
        == (if x == c { v } else { last_val(s, x) }) by {
        lemma_last_val_push(s, c, v, x);
    }

    assert forall |y: int| #[trigger] in_u64(y) implies
        ((exists |i: int| 0 <= i < sp.len() && sp[i].0 == y as u64)
         <==> ((exists |i: int| 0 <= i < s.len() && s[i].0 == y as u64) || y == c as int)) by {
        lemma_int_roundtrip(y);
        lemma_u64_roundtrip(c);

        if exists |i: int| 0 <= i < sp.len() && sp[i].0 == y as u64 {
            let i = choose |i: int| 0 <= i < sp.len() && sp[i].0 == y as u64;
            if i < s.len() {
                assert(sp[i] == s[i]);
                assert(s[i].0 == y as u64);
            } else {
                assert(i == s.len());
                assert(sp[i] == (c, v));
                assert((y as u64) == c);
                assert(y == c as int);
            }
        }

        if exists |i: int| 0 <= i < s.len() && s[i].0 == y as u64 {
            let i = choose |i: int| 0 <= i < s.len() && s[i].0 == y as u64;
            assert(sp[i] == s[i]);
            assert(0 <= i < sp.len() && sp[i].0 == y as u64);
        }

        if y == c as int {
            assert((y as u64) == c);
            assert(sp[s.len() as int] == (c, v));
            assert(0 <= (s.len() as int) < sp.len() && sp[s.len() as int].0 == y as u64);
        }
    }
    assert(writes_set(sp) =~= writes_set(s).insert(c as int));
    assert(writes_map(sp) =~= writes_map(s).insert(c as int, v as int));
}

pub proof fn lemma_publish_push(cv: Map<int, int>, s: Seq<(u64, u64)>, c: u64, v: u64)
    ensures
        publish_writes(cv, writes_set(s.push((c, v))), writes_map(s.push((c, v))))
            =~= publish_writes(cv, writes_set(s), writes_map(s)).insert(c as int, v as int),
{
    lemma_writes_push(s, c, v);
    let ws = writes_set(s);
    let wv = writes_map(s);
    let cc = c as int;
    let vv = v as int;
    assert(writes_set(s.push((c, v))) =~= ws.insert(cc));
    assert(writes_map(s.push((c, v))) =~= wv.insert(cc, vv));
    assert(publish_writes(cv, ws.insert(cc), wv.insert(cc, vv))
           =~= publish_writes(cv, ws, wv).insert(cc, vv));
}

pub proof fn lemma_publish_writer_push(cw: Map<int, int>, s: Seq<(u64, u64)>, writer: int, c: u64, v: u64)
    ensures
        publish_writer(cw, writes_set(s.push((c, v))), writer)
            =~= publish_writer(cw, writes_set(s), writer).insert(c as int, writer),
{
    lemma_writes_push(s, c, v);
    let ws = writes_set(s);
    let cc = c as int;
    assert(writes_set(s.push((c, v))) =~= ws.insert(cc));
    assert(publish_writer(cw, ws.insert(cc), writer)
           =~= publish_writer(cw, ws, writer).insert(cc, writer));
}

pub struct L2Runtime {
    pub now:         u64,
    pub txns:        HashMapWithView<u64, ExecTxn>,
    pub cell_value:  HashMapWithView<u64, u64>,
    pub cell_writer: HashMapWithView<u64, u64>,
    pub next_txn:    u64,
}

impl L2Runtime {
    pub open spec fn view(self) -> RuntimeState {
        RuntimeState {
            now:         self.now as int,
            txns:        view_txns_map(self.txns@),
            cell_value:  view_u64_map(self.cell_value@),
            cell_writer: view_u64_map(self.cell_writer@),
            all_txns:    view_alltxns(self.txns@),
        }
    }

    pub open spec fn fresh_ok(self) -> bool {
        forall |k: u64| #[trigger] self.txns@.contains_key(k) ==> (k as int) < (self.next_txn as int)
    }

    pub open spec fn keys_contiguous(self) -> bool {
        forall |k: u64| #[trigger] self.txns@.contains_key(k)
            <==> (k as int) < (self.next_txn as int)
    }

    pub open spec fn wf(self) -> bool {
        &&& inv_l2(self.view())
        &&& self.fresh_ok()
        &&& self.keys_contiguous()
    }

    pub fn new() -> (r: L2Runtime)
        ensures r.wf(), r.view() == initial_state(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let r = L2Runtime {
            now: 0,
            txns:        HashMapWithView::new(),
            cell_value:  HashMapWithView::new(),
            cell_writer: HashMapWithView::new(),
            next_txn: 0,
        };
        proof {
            assert(view_txns_map(r.txns@) =~= Map::<int, TxnState>::empty());
            assert(view_alltxns(r.txns@) =~= Set::<int>::empty());
            assert(view_u64_map(r.cell_value@) =~= Map::<int, int>::empty());
            assert(view_u64_map(r.cell_writer@) =~= Map::<int, int>::empty());
            assert(r.view() =~= initial_state());
            lemma_initial_inv_l2();
            assert(inv_l2(r.view()));
            assert(r.keys_contiguous());
        }
        r
    }

    pub fn begin(&mut self) -> (t: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).next_txn < u64::MAX,
        ensures
            final(self).wf(),
            final(self).view() == step_begin(old(self).view(), t as int),
            !old(self).txns@.contains_key(t),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let t = self.next_txn;

        proof {
            assert(!self.txns@.contains_key(t));
            assert(!view_txns_map(self.txns@).contains_key(t as int)) by {
                lemma_u64_roundtrip(t);
            }
        }

        let rec = ExecTxn::new_started();
        let ghost old_txns = self.txns@;
        self.txns.insert(t, rec);
        self.now = self.now + 1;
        self.next_txn = self.next_txn + 1;
        proof {
            assert(self.txns@ =~= old_txns.insert(t, rec));
            lemma_view_txns_insert(old_txns, t, rec);
            assert(self.view().txns =~= step_begin(old(self).view(), t as int).txns);
            assert(self.view().all_txns =~= step_begin(old(self).view(), t as int).all_txns);
            assert(self.view() =~= step_begin(old(self).view(), t as int));
            lemma_begin_preserves_inv_l2(old(self).view(), t as int);
            assert(inv_l2(self.view()));
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                if kk != t {
                    assert(old_txns.contains_key(kk));
                }
            }

            assert(t == old(self).next_txn);
            assert(self.next_txn == old(self).next_txn + 1);
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                if self.txns@.contains_key(k) {
                    if k != t {
                        assert(old_txns.contains_key(k));
                        assert((k as int) < (old(self).next_txn as int));
                    }
                }
                if (k as int) < (self.next_txn as int) {
                    if k != t {
                        assert((k as int) < (old(self).next_txn as int));
                        assert(old(self).txns@.contains_key(k));
                    }
                }
            }
        }
        t
    }

    // write: record a single write (cell c := value v) in txn t's write-set.
    pub fn write(&mut self, t: u64, c: u64, v: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
            !old(self).txns@[t].committed,
        ensures
            final(self).wf(),
            final(self).view()
                == step_write(old(self).view(), t as int, c as int, v as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_txns = self.txns@;
        let ghost old_view = self.view();
        let ghost old_txn = old_txns[t];
        // Take the txn out, modify its write-set/values, put it back.
        let mut txn = self.txns.remove(&t).unwrap();
        txn.writes.push((c, v));
        self.txns.insert(t, txn);
        self.now = self.now + 1;
        proof {
            lemma_u64_roundtrip(t);
            // The removed record is the model's txns[t].
            assert(old_view.txns[t as int] == old_txn.view());
            // Write-Vec push congruence.
            lemma_writes_push(old_txn.writes@, c, v);
            // The reinserted record's view is step_write's new_txn.
            assert(txn.view() =~= TxnState {
                write_set: old_view.txns[t as int].write_set.insert(c as int),
                write_values: old_view.txns[t as int].write_values.insert(c as int, v as int),
                ..old_view.txns[t as int]
            });
            // remove-then-insert on the same key == insert.
            assert(self.txns@ =~= old_txns.insert(t, txn));
            lemma_view_txns_insert(old_txns, t, txn);
            assert(self.view() =~= step_write(old_view, t as int, c as int, v as int));
            // Preservation via the existing model lemma.
            lemma_write_preserves_inv_l2(old_view, t as int, c as int, v as int);
            assert(inv_l2(self.view()));
            // fresh_ok preserved: key set unchanged (t was already present).
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(old_txns.contains_key(kk) || kk == t);
            }
            // keys_contiguous preserved: key set unchanged (remove-then-insert
            // of the same key t) and next_txn untouched.
            assert(self.txns@.dom() =~= old_txns.dom());
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> old_txns.contains_key(k));
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }
    }

    // commit: publish txn t's writes and mark it committed. Refines
    // step_commit; preserves wf via lemma_commit_preserves_inv_l2. The
    // discipline (only commit when valid) is the commit_valid precondition.
    pub fn commit(&mut self, t: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
            commit_valid(old(self).view(), t as int),
        ensures
            final(self).wf(),
            final(self).view() == step_commit(old(self).view(), t as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_view = self.view();
        let ghost old_txns = self.txns@;
        let ghost old_cv = old_view.cell_value;
        let ghost old_cw = old_view.cell_writer;
        let ghost txn0 = old_txns[t];
        proof { lemma_u64_roundtrip(t); }

        // Remove the txn (own it), mark committed, iterate its writes while it
        // is OUT of the map (no clone, no borrow conflict), reinsert after.
        let mut txn = self.txns.remove(&t).unwrap();
        txn.committed = true;
        txn.commit_time = self.now;

        proof {
            assert(self.txns@ =~= old_txns.remove(t));
            assert(txn.writes@ =~= txn0.writes@);
            // Base case: the empty prefix publishes to the original maps.
            assert(txn.writes@.subrange(0, 0) =~= Seq::<(u64, u64)>::empty());
            assert(publish_writes(old_cv, writes_set(txn.writes@.subrange(0, 0)),
                                  writes_map(txn.writes@.subrange(0, 0))) =~= old_cv);
            assert(publish_writer(old_cw, writes_set(txn.writes@.subrange(0, 0)),
                                  t as int) =~= old_cw);
            assert(view_u64_map(self.cell_value@) =~= old_cv);
            assert(view_u64_map(self.cell_writer@) =~= old_cw);
        }

        let mut i: usize = 0;
        while i < txn.writes.len()
            invariant
                0 <= i <= txn.writes.len(),
                txn.writes@ == txn0.writes@,
                self.txns@ == old_txns.remove(t),
                self.now == old(self).now,
                self.next_txn == old(self).next_txn,
                view_u64_map(self.cell_value@)
                    == publish_writes(old_cv, writes_set(txn.writes@.subrange(0, i as int)),
                                      writes_map(txn.writes@.subrange(0, i as int))),
                view_u64_map(self.cell_writer@)
                    == publish_writer(old_cw, writes_set(txn.writes@.subrange(0, i as int)),
                                      t as int),
            decreases txn.writes.len() - i
        {
            let ghost prefix = txn.writes@.subrange(0, i as int);
            let c = txn.writes[i].0;
            let v = txn.writes[i].1;
            let ghost cv_before = self.cell_value@;
            let ghost cw_before = self.cell_writer@;
            proof {
                assert(txn.writes@[i as int] == (c, v));
                assert(txn.writes@.subrange(0, (i + 1) as int) =~= prefix.push((c, v)));
            }
            self.cell_value.insert(c, v);
            self.cell_writer.insert(c, t);
            proof {
                lemma_view_map_insert(cv_before, c, v);
                lemma_view_map_insert(cw_before, c, t);
                lemma_publish_push(old_cv, prefix, c, v);
                lemma_publish_writer_push(old_cw, prefix, t as int, c, v);
            }
            i = i + 1;
        }

        let ghost gtxn = txn;
        proof {
            assert(txn.writes@.subrange(0, i as int) =~= txn.writes@);
            assert(view_u64_map(self.cell_value@)
                == publish_writes(old_cv, writes_set(gtxn.writes@), writes_map(gtxn.writes@)));
            assert(view_u64_map(self.cell_writer@)
                == publish_writer(old_cw, writes_set(gtxn.writes@), t as int));
        }
        self.txns.insert(t, txn);
        self.now = self.now + 1;

        proof {
            assert(self.txns@ =~= old_txns.insert(t, gtxn));
            assert(gtxn.writes@ =~= txn0.writes@);
            // write_set / write_values of the model txn are exactly the Vec views.
            assert(txn0.view().write_set == writes_set(txn0.writes@));
            assert(txn0.view().write_values == writes_map(txn0.writes@));
            // The committed record is step_commit's new_txn.
            assert(gtxn.view() =~= TxnState {
                committed: true,
                commit_time: old_view.now,
                ..txn0.view()
            });
            lemma_view_txns_insert(old_txns, t, gtxn);
            // Assemble: every field of the view matches step_commit.
            let sc = step_commit(old_view, t as int);
            assert(self.view().now == sc.now);
            assert(self.view().txns =~= sc.txns);
            assert(self.view().cell_value =~= sc.cell_value);
            assert(self.view().cell_writer =~= sc.cell_writer);
            assert(self.view().all_txns =~= sc.all_txns);
            assert(self.view() == sc);
            lemma_commit_preserves_inv_l2(old_view, t as int);
            assert(inv_l2(self.view()));
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(old_txns.contains_key(kk) || kk == t);
            }
            // keys_contiguous preserved: key set unchanged (remove-then-insert
            // of the same key t) and next_txn untouched.
            assert(self.txns@.dom() =~= old_txns.dom());
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> old_txns.contains_key(k));
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }
    }

    // read: txn t reads cell c. Records the value and provenance (writer),
    // stamps the read time, and unions the writer's causal closure into t's
    // predecessors so that one-level cascade_abort is sufficient. Refines
    // step_read; preserves wf via lemma_read_preserves_inv_l2.
    pub fn read(&mut self, t: u64, c: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
            old(self).cell_value@.contains_key(c),
            !old(self).txns@[t].committed,
        ensures
            final(self).wf(),
            final(self).view() == step_read(old(self).view(), t as int, c as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_view = self.view();
        let ghost old_txns = self.txns@;
        let ghost txn0 = old_txns[t];

        // c has a recorded value and (by inv_l2) a known, committed writer.
        let v: u64 = *self.cell_value.get(&c).unwrap();
        proof {
            lemma_u64_roundtrip(t);
            lemma_u64_roundtrip(c);
            // inv_cell_domains: cell_value has c => cell_writer has c.
            assert(self.cell_value@.contains_key(c));
            assert(old_view.cell_value.contains_key(c as int)) by { lemma_int_roundtrip(c as int); }
            assert(self.cell_writer@.contains_key(c));
        }
        let writer: u64 = *self.cell_writer.get(&c).unwrap();
        proof {
            lemma_u64_roundtrip(writer);
            lemma_int_roundtrip(c as int);
            assert(self.cell_writer@[c] == writer);
            assert(self.cell_value@[c] == v);
            // view-level value/writer agree with v / writer (via view_u64_map).
            // Establishing the cell_writer[c as int] term FIRST fires the
            // inv_writers_committed trigger below.
            assert(old_view.cell_value[c as int] == v as int);
            assert(old_view.cell_writer[c as int] == writer as int);
            // inv_writers_committed(old_view): the writer is a known committed
            // txn (instantiated at c as int via the cell_writer[c as int] term).
            assert(inv_writers_committed(old_view));
            assert(old_view.txns.contains_key(writer as int));
            assert(self.txns@.contains_key(writer)) by { lemma_u64_roundtrip(writer); }
        }

        // Copy the writer's predecessor Vec out. Works whether writer == t or
        // not, because t is still in the map at this point.
        let ghost wpred = self.txns@[writer].predecessors@;
        let wlen: usize = self.txns.get(&writer).unwrap().predecessors.len();
        let mut wpred_copy: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < wlen
            invariant
                0 <= i <= wlen,
                self.txns@ == old_txns,
                self.txns@.contains_key(writer),
                wpred == self.txns@[writer].predecessors@,
                wlen == wpred.len(),
                wpred_copy@ == wpred.subrange(0, i as int),
            decreases wlen - i
        {
            let x: u64 = self.txns.get(&writer).unwrap().predecessors[i];
            proof { assert(wpred[i as int] == x); }
            wpred_copy.push(x);
            proof {
                assert(wpred.subrange(0, (i + 1) as int) =~= wpred.subrange(0, i as int).push(x));
            }
            i = i + 1;
        }
        proof { assert(wpred_copy@ =~= wpred); }

        // Take t out and build its new record.
        let mut txn = self.txns.remove(&t).unwrap();
        let ghost old_t_pred = txn.predecessors@;
        proof { assert(old_t_pred =~= txn0.predecessors@); }

        // predecessors := old ++ [writer] ++ wpred_copy.
        let ghost before0 = txn.predecessors@;
        txn.predecessors.push(writer);
        proof {
            lemma_vec_set_push(before0, writer);
            lemma_vec_set_empty();
            assert(wpred_copy@.subrange(0, 0) =~= Seq::<u64>::empty());
            assert(view_vec_u64_set(txn.predecessors@)
                =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                    .union(view_vec_u64_set(wpred_copy@.subrange(0, 0))));
        }
        let mut j: usize = 0;
        while j < wpred_copy.len()
            invariant
                0 <= j <= wpred_copy.len(),
                wpred_copy@ == wpred,
                // only predecessors changes in this loop; pin the rest.
                txn.read_set@ == txn0.read_set@,
                txn.read_values@ == txn0.read_values@,
                txn.read_from@ == txn0.read_from@,
                txn.read_at@ == txn0.read_at@,
                txn.writes@ == txn0.writes@,
                txn.started == txn0.started,
                txn.committed == txn0.committed,
                txn.aborted == txn0.aborted,
                txn.commit_time == txn0.commit_time,
                view_vec_u64_set(txn.predecessors@)
                    == view_vec_u64_set(old_t_pred).insert(writer as int)
                       .union(view_vec_u64_set(wpred_copy@.subrange(0, j as int))),
            decreases wpred_copy.len() - j
        {
            let y: u64 = wpred_copy[j];
            let ghost before = txn.predecessors@;
            txn.predecessors.push(y);
            proof {
                lemma_vec_set_push(before, y);
                assert(wpred_copy@.subrange(0, (j + 1) as int)
                    =~= wpred_copy@.subrange(0, j as int).push(y));
                lemma_vec_set_push(wpred_copy@.subrange(0, j as int), y);
                // A.union(B.insert(y)) == A.union(B).insert(y)
                assert(view_vec_u64_set(txn.predecessors@)
                    =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                        .union(view_vec_u64_set(wpred_copy@.subrange(0, (j + 1) as int))));
            }
            j = j + 1;
        }
        proof {
            assert(wpred_copy@.subrange(0, j as int) =~= wpred_copy@);
            assert(view_vec_u64_set(txn.predecessors@)
                =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                    .union(view_vec_u64_set(wpred)));
        }

        // read_set, read_values, read_from, read_at.
        let ghost rs0 = txn.read_set@;
        txn.read_set.insert(c);
        proof { lemma_view_set_insert(rs0, c); }
        let ghost rv0 = txn.read_values@;
        txn.read_values.insert(c, v);
        proof { lemma_view_map_insert(rv0, c, v); }
        let ghost rf0 = txn.read_from@;
        txn.read_from.insert(c, writer);
        proof { lemma_view_map_insert(rf0, c, writer); }
        let ghost ra0 = txn.read_at@;
        txn.read_at.insert(c, self.now);
        proof {
            assert(self.now as int == old_view.now);
            lemma_view_map_insert(ra0, c, self.now);
        }

        let ghost gtxn = txn;
        self.txns.insert(t, txn);
        self.now = self.now + 1;

        proof {
            // The new record is step_read's new_txn (field by field).
            assert(old_view.txns[t as int] == txn0.view());
            assert(old_view.txns[writer as int].predecessors =~= view_vec_u64_set(wpred));
            // bridges: the captured ghosts equal txn0's fields (the other
            // inserts did not touch them); predecessor closure carries to gtxn.
            assert(rs0 =~= txn0.read_set@);
            assert(rv0 =~= txn0.read_values@);
            assert(rf0 =~= txn0.read_from@);
            assert(ra0 =~= txn0.read_at@);
            assert(txn0.view().predecessors =~= view_vec_u64_set(old_t_pred));
            assert(view_vec_u64_set(gtxn.predecessors@)
                =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                    .union(view_vec_u64_set(wpred)));
            assert(gtxn.view() =~= TxnState {
                read_set:     txn0.view().read_set.insert(c as int),
                read_values:  txn0.view().read_values.insert(c as int, v as int),
                predecessors: txn0.view().predecessors.insert(writer as int)
                                  .union(old_view.txns[writer as int].predecessors),
                read_from:    txn0.view().read_from.insert(c as int, writer as int),
                read_at:      txn0.view().read_at.insert(c as int, old_view.now),
                ..txn0.view()
            });
            assert(self.txns@ =~= old_txns.insert(t, gtxn));
            lemma_view_txns_insert(old_txns, t, gtxn);
            let sr = step_read(old_view, t as int, c as int);
            assert(self.view().now == sr.now);
            assert(self.view().txns =~= sr.txns);
            assert(self.view().cell_value =~= sr.cell_value);
            assert(self.view().cell_writer =~= sr.cell_writer);
            assert(self.view().all_txns =~= sr.all_txns);
            assert(self.view() == sr);
            // Preservation via the existing model lemma.
            lemma_read_preserves_inv_l2(old_view, t as int, c as int);
            assert(inv_l2(self.view()));
            // fresh_ok + keys_contiguous: key set and next_txn unchanged.
            assert(self.txns@.dom() =~= old_txns.dom());
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(old_txns.contains_key(kk) || kk == t);
            }
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> old_txns.contains_key(k));
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }
    }

    // Linear scan: does txn u's predecessor Vec contain t?
    fn txn_pred_contains(&self, u: u64, t: u64) -> (r: bool)
        requires self.txns@.contains_key(u),
        ensures r <==> view_vec_u64_set(self.txns@[u].predecessors@).contains(t as int),
    {
        let n: usize = self.txns.get(&u).unwrap().predecessors.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                self.txns@.contains_key(u),
                n == self.txns@[u].predecessors@.len(),
                forall |k: int| 0 <= k < i ==> self.txns@[u].predecessors@[k] != t,
            decreases n - i
        {
            if self.txns.get(&u).unwrap().predecessors[i] == t {
                proof { lemma_vec_set_contains_iff(self.txns@[u].predecessors@, t); }
                return true;
            }
            i = i + 1;
        }
        proof { lemma_vec_set_contains_iff(self.txns@[u].predecessors@, t); }
        false
    }

    // abort: mark t aborted, then cascade-abort every txn whose (transitively
    // closed) predecessor set contains t. Keys are exactly [0, next_txn), so
    // the cascade is a single scan of that range. Refines step_abort; preserves
    // wf via lemma_abort_preserves_inv_l2.
    pub fn abort(&mut self, t: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
        ensures
            final(self).wf(),
            final(self).view() == step_abort(old(self).view(), t as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_view = self.view();
        let ghost old_txns = self.txns@;
        let ghost old_cv = self.cell_value@;
        let ghost old_cw = self.cell_writer@;

        // Step 1: mark t aborted.
        let mut txn_t = self.txns.remove(&t).unwrap();
        txn_t.aborted = true;
        let ghost gtxn_t = txn_t;
        self.txns.insert(t, txn_t);

        let ghost base_txns = self.txns@;
        let ghost base_view = view_txns_map(base_txns);
        proof {
            lemma_u64_roundtrip(t);
            assert(base_txns =~= old_txns.insert(t, gtxn_t));
            lemma_view_txns_insert(old_txns, t, gtxn_t);
            assert(gtxn_t.view() =~= TxnState { aborted: true, ..old_view.txns[t as int] });
            assert(base_view =~= old_view.txns.insert(t as int,
                TxnState { aborted: true, ..old_view.txns[t as int] }));
            // base keys are exactly [0, next_txn).
            assert forall |k: u64| #[trigger] base_txns.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(base_txns.contains_key(k) <==> old_txns.contains_key(k) || k == t);
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }

        // Step 2: single-pass cascade over [0, next_txn).
        let n: u64 = self.next_txn;
        let mut u: u64 = 0;
        while u < n
            invariant
                0 <= u <= n,
                n == self.next_txn,
                self.now == old(self).now,
                self.cell_value@ == old_cv,
                self.cell_writer@ == old_cw,
                self.txns@.dom() == base_txns.dom(),
                forall |k: u64| #[trigger] base_txns.contains_key(k) <==> (k as int) < (n as int),
                forall |k: u64| #[trigger] base_txns.contains_key(k) ==>
                    self.txns@.contains_key(k)
                    && self.txns@[k].view() == (
                        if (k as int) < (u as int)
                           && base_txns[k].view().predecessors.contains(t as int) {
                            TxnState { aborted: true, ..base_txns[k].view() }
                        } else {
                            base_txns[k].view()
                        }),
            decreases n - u
        {
            let ghost pre = self.txns@;
            proof {
                // u is in range, so it is a live key and still equals base[u].
                assert(base_txns.contains_key(u));
                assert(self.txns@.contains_key(u));
                assert(self.txns@[u].view() == base_txns[u].view());
            }
            let has_t: bool = self.txn_pred_contains(u, t);
            proof {
                assert(has_t <==> base_txns[u].view().predecessors.contains(t as int));
            }
            if has_t {
                let mut ut = self.txns.remove(&u).unwrap();
                proof { assert(ut == pre[u]); }
                ut.aborted = true;
                let ghost gut = ut;
                self.txns.insert(u, ut);
                proof {
                    assert(self.txns@ =~= pre.insert(u, gut));
                    assert(gut.view() =~= TxnState { aborted: true, ..base_txns[u].view() });
                    assert forall |k: u64| #[trigger] base_txns.contains_key(k) implies
                        self.txns@.contains_key(k)
                        && self.txns@[k].view() == (
                            if (k as int) < ((u + 1) as int)
                               && base_txns[k].view().predecessors.contains(t as int) {
                                TxnState { aborted: true, ..base_txns[k].view() }
                            } else {
                                base_txns[k].view()
                            }) by {
                        if k == u {
                            assert(self.txns@[u] == gut);
                        } else {
                            assert(self.txns@[k] == pre[k]);
                        }
                    }
                }
            } else {
                proof {
                    assert forall |k: u64| #[trigger] base_txns.contains_key(k) implies
                        self.txns@.contains_key(k)
                        && self.txns@[k].view() == (
                            if (k as int) < ((u + 1) as int)
                               && base_txns[k].view().predecessors.contains(t as int) {
                                TxnState { aborted: true, ..base_txns[k].view() }
                            } else {
                                base_txns[k].view()
                            }) by {
                        if k == u {
                            assert(!base_txns[u].view().predecessors.contains(t as int));
                            assert(self.txns@[u].view() == base_txns[u].view());
                        }
                    }
                }
            }
            u = u + 1;
        }

        self.now = self.now + 1;

        proof {
            let ca = cascade_abort(base_view, t as int);
            // view of the final txn store == cascade_abort(base_view, t).
            assert forall |id: int| #[trigger] view_txns_map(self.txns@).contains_key(id)
                implies view_txns_map(self.txns@)[id] == ca[id] by {
                if in_u64(id) && self.txns@.contains_key(id as u64) {
                    let k = id as u64;
                    lemma_int_roundtrip(id);
                    assert(base_txns.contains_key(k));
                    assert((k as int) < (n as int));
                    assert(base_view[id] == base_txns[k].view());
                }
            }
            assert(view_txns_map(self.txns@).dom() =~= ca.dom());
            assert(view_txns_map(self.txns@) =~= ca);
            let sa = step_abort(old_view, t as int);
            assert(self.view().now == sa.now);
            assert(self.view().txns =~= sa.txns);
            assert(self.view().cell_value =~= sa.cell_value);
            assert(self.view().cell_writer =~= sa.cell_writer);
            assert(self.view().all_txns =~= sa.all_txns);
            assert(self.view() == sa);
            // Preservation via the existing model lemma.
            lemma_abort_preserves_inv_l2(old_view, t as int);
            assert(inv_l2(self.view()));
            // fresh_ok + keys_contiguous: key set and next_txn unchanged.
            assert(self.txns@.dom() =~= base_txns.dom());
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(base_txns.contains_key(kk));
            }
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> base_txns.contains_key(k));
            }
        }
    }

    // CAPSTONE: any wf runtime is A_3-free. Holds now for the new+begin
    // fragment; once commit/abort (iterations 2-3) are shown to preserve wf,
    // this theorem covers the full runtime unchanged.
    pub fn a3_free(&self)
        requires self.wf(),
        ensures forall |t: TxnId| #![trigger self.view().txns[t].committed]
            !a3_witness(self.view(), t),
    {
        proof {
            lemma_l2_reachable_no_a3(self.view());
        }
    }
}
} // verus!
