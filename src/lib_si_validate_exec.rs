use vstd::prelude::*;

verus! {

pub type Cell = usize;
pub type Val = usize;


pub open spec fn in_set(rs: Seq<Cell>, c: Cell) -> bool {
    exists|i: int| 0 <= i < rs.len() && rs[i] == c
}

pub open spec fn fresh(vs: Seq<(Cell, u64, Val)>, rs: Seq<Cell>, rt: u64) -> bool {
    forall|k: int|
        0 <= k < vs.len() ==> (in_set(rs, vs[k].0) ==> vs[k].1 <= rt)
}
    
pub fn contains(rs: &Vec<Cell>, c: Cell) -> (b: bool)
    ensures b == in_set(rs@, c)
{
    let n = rs.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == rs@.len(),
            forall|t: int| 0 <= t < k ==> rs@[t] != c,
        decreases n - k
    {
        if rs[k] == c {
            assert(rs@[k as int] == c);
            return true;
        }
        k = k + 1;
    }
    false
}
    
pub fn validate(vs: &Vec<(Cell, u64, Val)>, rs: &Vec<Cell>, rt: u64) -> (ok: bool)
    ensures ok == fresh(vs@, rs@, rt)
{
    let n = vs.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == vs@.len(),
            forall|t: int|
                0 <= t < k ==> (in_set(rs@, vs@[t].0) ==> vs@[t].1 <= rt),
        decreases n - k
    {
        let c = vs[k].0;
        let t = vs[k].1;
        let inset = contains(rs, c);
        if inset && t > rt {
            // Witnesses !fresh at index k.
            assert(in_set(rs@, vs@[k as int].0));
            assert(vs@[k as int].1 > rt);
            return false;
        }

        assert(in_set(rs@, vs@[k as int].0) ==> vs@[k as int].1 <= rt);
        k = k + 1;
    }

    true
}
    
pub proof fn fresh_means_no_overwrite(
    vs: Seq<(Cell, u64, Val)>, rs: Seq<Cell>, rt: u64, c: Cell, idx: int
)
    requires
        fresh(vs, rs, rt),
        in_set(rs, c),
        0 <= idx < vs.len(),
        vs[idx].0 == c,
    ensures
        vs[idx].1 <= rt,
{
}

} // verus!