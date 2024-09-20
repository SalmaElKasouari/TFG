include "Ord.dfy"

/*
 *  mapSeq applies the function f to all the elements in the segment
 *  [startIdx, endIdx) of the input sequence a.
 */
ghost function mapSeq<T,R>(a: seq<T>, f: T -> R, startIdx: nat, endIdx: nat): (output: seq<R>)
	requires 0 <= startIdx <= endIdx <= |a|
	ensures |output| == endIdx-startIdx
	ensures forall i: nat | 0 <= i < |output| :: output[i] == f(a[startIdx + i])
	decreases endIdx - startIdx
{
  if(startIdx == endIdx) then []
  else [f(a[startIdx])] + mapSeq(a, f, startIdx + 1, endIdx)
}

lemma mapSeqConcatChg<T,R>(a: seq<T>, b: seq<T>, f: T->R) // Generalize to startIdx, endIdx?
	ensures mapSeq(a+b, f, 0, |a+b|) == mapSeq(a, f, 0, |a|) + mapSeq(b, f, 0, |b|)
{}

/*
 * selectSeq "selects" elements in sequence a, whose position contains a true in the
 * "b" sequence
 */
ghost function selectSeq<T>(a: seq<T>, b: seq<bool>, startIdx: nat, endIdx: nat): (output: seq<T>)
	requires 0 <= startIdx <= endIdx <= |a|// == |b|
	requires endIdx <= |b|
	ensures |output| <= (endIdx-startIdx) <= |a|
	ensures forall i: nat | 0 <= i < |output| :: output[i] in a
	ensures forall i: nat | startIdx <= i < endIdx :: b[i] == true ==> a[i] in output
	decreases endIdx - startIdx
{
  if(startIdx == endIdx) then []
  else (if(b[startIdx]) then [a[startIdx]] else []) + selectSeq(a, b, startIdx + 1, endIdx)
}

lemma selectSeqZero<T>(a: seq<T>, b: seq<bool>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|// == |b|
	requires endIdx <= |b|
	requires forall i: nat | startIdx <= i < endIdx :: b[i] == false
	ensures selectSeq(a, b, startIdx, endIdx) == []
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) {
		assert selectSeq(a, b, startIdx, endIdx) == [];
	} else {
		selectSeqZero(a, b, startIdx+1, endIdx);
		assert b[startIdx] == false;
	}
}


/*
 * If 2 boolean sequences are equal in the segment [startIdx, endIdx), then the selectSeq
 * with each sequence is the same
 */
lemma selectSeqEqualB<T>(a: seq<T>, b1: seq<bool>, b2: seq<bool>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|// == |b1| == |b2|
	requires endIdx <= |b1|
	requires endIdx <= |b2|
	requires forall i: nat | startIdx <= i < endIdx :: b1[i] == b2[i]
	ensures  selectSeq(a, b1, startIdx, endIdx) == selectSeq(a, b2, startIdx, endIdx)
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) {
		calc == {
			selectSeq(a, b1, startIdx, endIdx);
			[];
			selectSeq(a, b2, startIdx, endIdx);
		}
	} else {
		selectSeqEqualB(a, b1, b2, startIdx+1, endIdx);
		assert selectSeq(a, b1, startIdx+1, endIdx) == selectSeq(a, b2, startIdx+1, endIdx);
	}
}


/*
 * If a false in "b" is transformed into true, then the corresponding element in "a"
 * is added to the output
 */
lemma selectSeqDif<T>(a: seq<T>, b: seq<bool>, difIdx: nat, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= difIdx < endIdx <= |a| == |b|
	requires b[difIdx] == false
	ensures selectSeq(a, b[difIdx := true], startIdx, endIdx) == selectSeq(a, b, startIdx, difIdx) + [a[difIdx]] + selectSeq(a, b, difIdx+1, endIdx)
	decreases endIdx - startIdx
{
	if(startIdx == endIdx-1) {
		assert difIdx == startIdx;
		calc == {
			selectSeq(a, b[difIdx := true], startIdx, endIdx);
			[a[difIdx]] + selectSeq(a, b, startIdx+1, endIdx); {assert b[difIdx] == false;}
			[a[difIdx]] + selectSeq(a, b, startIdx, endIdx);
		}
	} else if(difIdx == startIdx){
		assert selectSeq(a, b[startIdx := true], startIdx, endIdx) == [a[difIdx]] + selectSeq(a, b[startIdx := true], startIdx+1, endIdx);
		selectSeqEqualB(a, b, b[startIdx := true], startIdx+1, endIdx);
	} else {
		selectSeqDif(a, b, difIdx, startIdx + 1, endIdx);
	}
}

lemma selectSeqSplit<T>(a: seq<T>, b: seq<bool>, splitIdx: nat, startIdx: nat, endIdx: nat)
	decreases endIdx-startIdx
	requires startIdx <= splitIdx < endIdx <= |a|
	requires endIdx <= |b|
	ensures selectSeq(a, b, startIdx, endIdx) == selectSeq(a, b, startIdx, splitIdx) + selectSeq(a, b, splitIdx, endIdx)
{
	if(startIdx == splitIdx) {
		assert selectSeq(a, b, startIdx, splitIdx) == [];
		assert selectSeq(a, b, startIdx, endIdx) == selectSeq(a, b, splitIdx, endIdx);
		assert selectSeq(a, b, startIdx, endIdx) == selectSeq(a, b, startIdx, splitIdx) + selectSeq(a, b, splitIdx, endIdx);
	} else {
		selectSeqSplit(a, b, splitIdx, startIdx+1, endIdx);
	}
}

/*
 * If a true in "b" is transformed into false, then the corresponding element in "a"
 * is not added to the output
 */
lemma selectSeqDecompose<T>(a: seq<T>, b: seq<bool>, difIdx: nat, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= difIdx < endIdx <= |a|// == |b|
	requires endIdx <= |b|
	requires b[difIdx] == false
	ensures selectSeq(a, b, startIdx, endIdx) == selectSeq(a, b, startIdx, difIdx) + selectSeq(a, b, difIdx+1, endIdx)
	decreases endIdx - startIdx
{
	if(startIdx == endIdx-1) {
		assert difIdx == startIdx;
		calc == {
			selectSeq(a, b[difIdx := false], startIdx, endIdx);
			selectSeq(a, b, startIdx+1, endIdx); {assert b[difIdx] == false;}
			selectSeq(a, b, startIdx+1, endIdx);
		}
	} else if(difIdx == startIdx){
		assert selectSeq(a, b[startIdx := false], startIdx, endIdx) == selectSeq(a, b[startIdx := false], startIdx+1, endIdx);
		selectSeqEqualB(a, b, b[startIdx := false], startIdx+1, endIdx);
	} else {
		selectSeqDecompose(a, b, difIdx, startIdx + 1, endIdx);
	}
}

ghost function filterSeq<T>(a:seq<T>, b: T -> bool, startIdx: nat, endIdx: nat): (output: seq<T>)
	requires 0 <= startIdx <= endIdx <= |a|
	ensures |output| <= (endIdx-startIdx) <= |a|
	ensures forall i: nat | 0 <= i < |output| :: output[i] in a && b(output[i]) == true
	decreases endIdx - startIdx
{
  if(startIdx == endIdx) then []
  else ((if(b(a[startIdx])) then [a[startIdx]] else []) + filterSeq(a, b, startIdx + 1, endIdx))
}
