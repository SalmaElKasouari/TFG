


predicate sorted_int(a: seq<int>)

{
	forall i: nat, j: nat | 0 <= i < j < |a| :: a[i] < a[j]
}


function min_int(a: int, b: int): (o: int)
	ensures o <= a
	ensures o <= b
	ensures o == a || o == b
{
	if(a < b) then a
	else b
}


function max_int(a: int, b: int): (o: int)
	ensures o >= a
	ensures o >= b
	ensures o == a || o == b
{
	if(a < b) then b
	else a
}


function max_real(a: real, b: real): (o: real)
	ensures o >= a
	ensures o >= b
	ensures o == a || o == b
{
	if(a < b) then b
	else a
}


function min_seq_int(a: seq<int>, startIdx: nat, endIdx: nat): (o: int)
	decreases endIdx - startIdx

	requires startIdx < endIdx
	requires endIdx <= |a|

	ensures forall i: nat | startIdx <= i < endIdx :: o <= a[i]
	ensures exists i: nat | startIdx <= i < endIdx :: o == a[i]
{
	if(startIdx+1 == endIdx) then a[startIdx]
	else min_int(a[startIdx], min_seq_int(a, startIdx+1, endIdx))
}

lemma min_seq_can_be_nat(a: seq<int>, startIdx: nat, endIdx: nat)
	requires startIdx < endIdx <= |a|
	requires forall i: nat | startIdx <= i < endIdx :: a[i] >= 0

	ensures min_seq_int(a, startIdx, endIdx) >= 0
{}

// If 2 sequences contains the same elements inside a range, then both min are equal
lemma min_seq_preserved_range(a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat)
	requires startIdx < endIdx <= |a|
	requires endIdx <= |b| // It's not required for both seqs to have the same length
	requires forall i: nat | startIdx <= i < endIdx :: a[i] == b[i]

	ensures min_seq_int(a, startIdx, endIdx) == min_seq_int(b, startIdx, endIdx)
{}
