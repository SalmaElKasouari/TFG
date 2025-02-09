include "Knapsack/Implementation/Item.dfy"

ghost function sumOfZipMultiply(a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat): int
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires startIdx <= endIdx
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) then 0
	else a[startIdx]*b[startIdx] + sumOfZipMultiply(a, b, startIdx + 1, endIdx)
}


lemma sumOfZipMultiplyNat(a: seq<nat>, b: seq<nat>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires startIdx <= endIdx
	ensures sumOfZipMultiply(a, b, startIdx, endIdx) >= 0
{
	if(startIdx == endIdx){
		assert sumOfZipMultiply(a, b, startIdx, endIdx) == 0 >= 0;
	} else {
		sumOfZipMultiplyNat(a, b, startIdx+1, endIdx);
		assert sumOfZipMultiply(a, b, startIdx+1, endIdx) >= 0;
		assert sumOfZipMultiply(a, b, startIdx, endIdx) == a[startIdx]*b[startIdx] + sumOfZipMultiply(a, b, startIdx+1, endIdx);
		assert a[startIdx]*b[startIdx] >= 0;
	}
}

lemma sumOfZipMultiplyZeroA(a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires startIdx <= endIdx
	requires forall idx: int | startIdx <= idx < |a| :: a[idx] == 0
	ensures sumOfZipMultiply(a, b, startIdx, endIdx) == 0
{}

// B version is the original
lemma sumOfZipMultiplyZeroB(a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires startIdx <= endIdx
	requires forall idx: int | startIdx <= idx < |b| :: b[idx] == 0
	ensures sumOfZipMultiply(a, b, startIdx, endIdx) == 0
{}

lemma sumOfZipMultiplyEqual(common: seq<int>, a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires endIdx <= |common|
	requires startIdx <= endIdx
	requires forall i: nat | startIdx <= i < endIdx :: a[i] == b[i]
	ensures sumOfZipMultiply(common, a, startIdx, endIdx) == sumOfZipMultiply(common, b, startIdx, endIdx)
{}

lemma sumOfZipMultiplyDecomposeRight(a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires startIdx < endIdx
	ensures sumOfZipMultiply(a, b, startIdx, endIdx) == sumOfZipMultiply(a, b, startIdx, endIdx-1) + a[endIdx-1] * b[endIdx-1]
{}

lemma sumOfZipMultiplySegmentEqualA(a: seq<int>, b: seq<int>, c: seq<int>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires endIdx <= |c|
	requires startIdx <= endIdx
	requires forall idx: nat | startIdx <= idx < endIdx :: a[idx] == c[idx]
	ensures sumOfZipMultiply(a, b, startIdx, endIdx) == sumOfZipMultiply(c, b, startIdx, endIdx)
{}

lemma sumOfZipMultiplySegmentEqualB(a: seq<int>, b: seq<int>, c: seq<int>, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires endIdx <= |c|
	requires startIdx <= endIdx
	requires forall idx: nat | startIdx <= idx < endIdx :: b[idx] == c[idx]
	ensures sumOfZipMultiply(a, b, startIdx, endIdx) == sumOfZipMultiply(a, c, startIdx, endIdx)
{}

lemma sumOfZipMultiplyDif(common: seq<int>, a: seq<int>, b: seq<int>, difIdx: nat, dif: int, startIdx: nat, endIdx: nat)
	decreases endIdx - startIdx
	requires endIdx <= |a|
	requires endIdx <= |b|
	requires endIdx <= |common|
	requires startIdx <= difIdx < endIdx
	requires forall i: nat | startIdx <= i < difIdx :: a[i] == b[i]
	requires forall i: nat | difIdx < i < endIdx :: a[i] == b[i]
	requires b[difIdx] == a[difIdx] + dif
	ensures sumOfZipMultiply(common, b, startIdx, endIdx) == sumOfZipMultiply(common, a, startIdx, endIdx) + dif*common[difIdx]
{
	if(startIdx == endIdx-1){
		assert startIdx <= difIdx < |a| ==> difIdx == startIdx;
		calc == {
			sumOfZipMultiply(common, b, startIdx, endIdx);
			common[startIdx] * b[startIdx];
			common[startIdx] * b[difIdx];
			common[startIdx] * (a[difIdx] + dif);
			common[startIdx] * a[difIdx] + common[startIdx] * dif;
			sumOfZipMultiply(common, a, startIdx, endIdx) + common[startIdx] * dif;
		}
	} else if(difIdx == startIdx){
		calc == {
			sumOfZipMultiply(common, b, startIdx, endIdx);
			common[startIdx] * b[startIdx] + sumOfZipMultiply(common, b, startIdx+1, endIdx);
			common[startIdx] * b[difIdx] + sumOfZipMultiply(common, b, startIdx+1, endIdx);
			common[startIdx] * (a[difIdx] + dif) + sumOfZipMultiply(common, b, startIdx+1, endIdx);
			common[startIdx] * a[difIdx] + common[startIdx] * dif + sumOfZipMultiply(common, b, startIdx+1, endIdx);
			common[startIdx] * a[difIdx] + sumOfZipMultiply(common, b, startIdx+1, endIdx) + common[startIdx] * dif; { sumOfZipMultiplySegmentEqualB(common, a, b, startIdx+1, endIdx); }
			common[startIdx] * a[difIdx] + sumOfZipMultiply(common, a, startIdx+1, endIdx) + common[startIdx] * dif;
			common[startIdx] * a[startIdx] + sumOfZipMultiply(common, a, startIdx+1, endIdx) + common[startIdx] * dif;
			sumOfZipMultiply(common, a, startIdx, endIdx) + common[startIdx] * dif;
		}
	} else {
		sumOfZipMultiplyDif(common, a, b, difIdx, dif, startIdx+1, endIdx);
		assert sumOfZipMultiply(common, b, startIdx+1, endIdx) == sumOfZipMultiply(common, a, startIdx+1, endIdx) + dif*common[difIdx];
		calc == {
			sumOfZipMultiply(common, b, startIdx, endIdx);
			common[startIdx] * b[startIdx] + sumOfZipMultiply(common, b, startIdx+1, endIdx);
			common[startIdx] * b[startIdx] + sumOfZipMultiply(common, a, startIdx+1, endIdx) + dif*common[difIdx];
			common[startIdx] * a[startIdx] + sumOfZipMultiply(common, a, startIdx+1, endIdx) + dif*common[difIdx];
			sumOfZipMultiply(common, a, startIdx, endIdx) + dif*common[difIdx];
		}
	}
}



ghost function sum(a: seq<int>, startIdx: nat, endIdx: nat): int
	requires 0 <= startIdx <= endIdx <= |a|
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) then 0
	else a[startIdx] + sum(a, startIdx + 1, endIdx)
}

lemma sumNotZero(a: seq<int>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall it: nat | startIdx <= it < endIdx :: a[it] >= 0
	ensures forall it: nat | startIdx <= it < endIdx :: sum(a, startIdx, endIdx) >= a[it]
	decreases endIdx - startIdx
{}

lemma sumSegmentEqual(a: seq<int>, b: seq<int>, startIdx: nat, endIdx: nat)
	requires |a| <= |b|
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall i: nat | startIdx <= i < endIdx :: a[i] == b[i]
	ensures sum(a, startIdx, endIdx) == sum(b, startIdx, endIdx)
	decreases endIdx - startIdx
{}

lemma sumDif(a: seq<int>, b: seq<int>, difIdx: nat, dif: int, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx < endIdx <= |a|
	requires startIdx <= difIdx < endIdx
	requires |a| == |b|
	requires forall i: nat | i < difIdx :: a[i] == b[i]
	requires forall i: nat | difIdx < i < |a| :: a[i] == b[i]
	requires b[difIdx] == a[difIdx] + dif
	ensures sum(b, startIdx, endIdx) == sum(a, startIdx, endIdx) + dif
	decreases endIdx - startIdx
{
	if(startIdx == endIdx-1) {
		calc == {
			sum(b, startIdx, endIdx);
			b[startIdx];
			b[difIdx];
			a[difIdx] + dif;
			a[startIdx] + dif;
			sum(a, startIdx, endIdx) + dif;
		}
	} else if(difIdx == startIdx) {
		calc == {
			sum(b, startIdx, endIdx);
			b[startIdx] + sum(b, startIdx + 1, endIdx);
			b[difIdx] + sum(b, startIdx + 1, endIdx);
			a[difIdx] + dif + sum(b, startIdx + 1, endIdx);
			a[startIdx] + dif + sum(b, startIdx + 1, endIdx); { sumSegmentEqual(a, b, startIdx+1, endIdx); }
			a[startIdx] + dif + sum(a, startIdx + 1, endIdx);
			a[startIdx] + sum(a, startIdx + 1, endIdx) + dif;
			sum(a, startIdx, endIdx) + dif;
		}
	} else {
		sumDif(a, b, difIdx, dif, startIdx + 1, endIdx);
		assert sum(b, startIdx+1, endIdx) == sum(a, startIdx+1, endIdx) + dif;
		calc == {
			sum(b, startIdx, endIdx);
			b[startIdx] + sum(b, startIdx+1, endIdx);
			b[startIdx] + sum(a, startIdx+1, endIdx) + dif;
			a[startIdx] + sum(a, startIdx+1, endIdx) + dif;
			sum(a, startIdx, endIdx) + dif;
		}
	}
}

lemma sumZero(a: seq<int>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall idx: int | startIdx <= idx < endIdx :: a[idx] == 0
	ensures sum(a, startIdx, endIdx) == 0
	decreases endIdx - startIdx
{}

lemma sumNat(a: seq<nat>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	ensures sum(a, startIdx, endIdx) >= 0
	decreases endIdx - startIdx
{}

lemma sumSubsegment(a: seq<int>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	ensures sum(a, startIdx, endIdx) == sum(a[startIdx..], 0, endIdx-startIdx)
	decreases endIdx-startIdx
{}

lemma sumSplit(a: seq<int>, startIdx: nat, endIdx: nat, idx: nat)
	requires 0 <= startIdx <= idx <= endIdx <= |a|
	ensures sum(a, startIdx, endIdx) == sum(a, startIdx, idx) + sum(a, idx, endIdx)
{
	if(startIdx == idx) {
		assert sum(a, startIdx, endIdx) == 0 + sum(a, idx, endIdx);
	} else {
		sumSplit(a, startIdx, endIdx, idx-1);
		calc == {
			sum(a, startIdx, endIdx);
			sum(a, startIdx, idx-1) + sum(a, idx-1, endIdx);
			sum(a, startIdx, idx-1) + (a[idx-1] + sum(a, idx, endIdx));
			(sum(a, startIdx, idx-1) + a[idx-1]) + sum(a, idx, endIdx);
			sum(a, startIdx, idx) + sum(a, idx, endIdx);
		}
	}
}

lemma sumConcat(a: seq<int>, b: seq<int>, startIdx: nat)
	requires 0 <= startIdx <= |a|
	ensures sum(a+b, startIdx, |a+b|) == sum(a, startIdx, |a|) + sum(b, 0, |b|)
	decreases |a|-startIdx
{
	if(startIdx == |a|) {
		assert sum(a, startIdx, |a|) == 0;
		assert forall i: nat | startIdx <= i < |a+b| :: (a+b)[i] == b[i-|a|];
		sumSegmentEqual((a+b)[startIdx..], b, 0, |b|);
		assert sum((a+b)[startIdx..], 0, |b|) == sum(b, 0, |b|);
		sumSubsegment(a+b, startIdx, |a+b|);
		assert sum((a+b)[startIdx..], 0, |b|) == sum((a+b), startIdx, |a+b|);
	} else {
		sumConcat(a, b, startIdx + 1);
	}
}

lemma sumDecomposeRight(a: seq<int>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx < endIdx <= |a|
	ensures sum(a, startIdx, endIdx) == sum(a, startIdx, endIdx-1) + a[endIdx-1]
{
	calc == {
		sum(a, startIdx, endIdx); {sumSplit(a, startIdx, endIdx, endIdx-1);}
		sum(a, startIdx, endIdx-1) + sum(a, endIdx-1, endIdx);
		sum(a, startIdx, endIdx-1) + a[endIdx-1];
	}
}

lemma sumNatMonotonic(a: seq<nat>, startIdx: nat, endIdx: nat, idx: nat)
	requires 0 <= startIdx <= idx <= endIdx <= |a|
	ensures sum(a, startIdx, idx) <= sum(a, startIdx, endIdx)
{
	if(idx == startIdx) {
		assert sum(a, startIdx, idx) == 0;
		sumNat(a, startIdx, endIdx);
	} else if(idx == endIdx) {
		assert sum(a, startIdx, idx) == sum(a, startIdx, endIdx);
	} else {
		sumSplit(a, startIdx, endIdx, idx);
		assert sum(a, startIdx, idx) + sum(a, idx, endIdx) == sum(a, startIdx, endIdx);
		sumNat(a, idx, endIdx);
	}
}

ghost function sumValue(a: seq<ItemData>, startIdx: int, endIdx: int) : real
  requires 0 <= startIdx <= endIdx <= |a|
  decreases endIdx - startIdx
{
  if(startIdx == endIdx) then 0.0
	else a[startIdx].value + sumValue(a, startIdx + 1, endIdx)
}

ghost function sum_real(a: seq<real>, startIdx: nat, endIdx: nat): real
	requires 0 <= startIdx <= endIdx <= |a|
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) then 0.0
	else a[startIdx] + sum_real(a, startIdx + 1, endIdx)
}


lemma sum_realSplit(a: seq<real>, startIdx: nat, endIdx: nat, idx: nat)
	requires 0 <= startIdx <= idx <= endIdx <= |a|
	ensures sum_real(a, startIdx, endIdx) == sum_real(a, startIdx, idx) + sum_real(a, idx, endIdx)
{
	if(startIdx == idx) {
		assert sum_real(a, startIdx, endIdx) == 0.0 + sum_real(a, idx, endIdx);
	} else {
		sum_realSplit(a, startIdx, endIdx, idx-1);
		calc == {
			sum_real(a, startIdx, endIdx);
			sum_real(a, startIdx, idx-1) + sum_real(a, idx-1, endIdx);
			sum_real(a, startIdx, idx-1) + (a[idx-1] + sum_real(a, idx, endIdx));
			(sum_real(a, startIdx, idx-1) + a[idx-1]) + sum_real(a, idx, endIdx);
			sum_real(a, startIdx, idx) + sum_real(a, idx, endIdx);
		}
	}
}

lemma sum_realSegmentEqual(a: seq<real>, b: seq<real>, startIdx: nat, endIdx: nat)
	requires |a| == |b|
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall i: nat | startIdx <= i < endIdx :: a[i] == b[i]
	ensures sum_real(a, startIdx, endIdx) == sum_real(b, startIdx, endIdx)
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) {
		assert sum_real(a, startIdx, endIdx) == sum_real(b, startIdx, endIdx) == 0.0;
	} else {
		sum_realSegmentEqual(a, b, startIdx + 1, endIdx);
		calc == {
			sum_real(b, startIdx, endIdx);
			b[startIdx] + sum_real(b, startIdx + 1, endIdx);
			b[startIdx] + sum_real(a, startIdx + 1, endIdx);
			a[startIdx] + sum_real(a, startIdx + 1, endIdx);
			sum_real(a, startIdx, endIdx);
		}
	}
}

lemma sum_realSubsegment(a: seq<real>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	ensures sum_real(a, startIdx, endIdx) == sum_real(a[startIdx..], 0, endIdx-startIdx)
	decreases endIdx-startIdx
{
	if(startIdx == endIdx) {
		assert sum_real(a, startIdx, endIdx) == 0.0;
		assert sum_real(a[startIdx..], 0, 0) == 0.0;
	} else {
		sum_realSubsegment(a, startIdx + 1, endIdx);
		assert sum_real(a, startIdx+1, endIdx) == sum_real(a[startIdx+1..], 0, endIdx-startIdx-1);
	}
}

lemma sum_realConcat(a: seq<real>, b: seq<real>, startIdx: nat)
	requires 0 <= startIdx <= |a|
	ensures sum_real(a+b, startIdx, |a+b|) == sum_real(a, startIdx, |a|) + sum_real(b, 0, |b|)
	decreases |a|-startIdx
{
	if(startIdx == |a|) {
		assert sum_real(a, startIdx, |a|) == 0.0;
		assert forall i: nat | startIdx <= i < |a+b| :: (a+b)[i] == b[i-|a|];
		sum_realSegmentEqual((a+b)[startIdx..], b, 0, |b|);
		assert sum_real((a+b)[startIdx..], 0, |b|) == sum_real(b, 0, |b|);
		sum_realSubsegment(a+b, startIdx, |a+b|);
		assert sum_real((a+b)[startIdx..], 0, |b|) == sum_real((a+b), startIdx, |a+b|);
	} else {
		sum_realConcat(a, b, startIdx + 1);
	}
}

lemma sum_realNotZero(a: seq<real>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall it: nat | startIdx <= it < endIdx :: a[it] >= 0.0
	ensures forall it: nat | startIdx <= it < endIdx :: sum_real(a, startIdx, endIdx) >= a[it]
	decreases endIdx - startIdx
{}

lemma sum_realZero(a: seq<real>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall idx: int | startIdx <= idx < endIdx :: a[idx] == 0.0
	ensures sum_real(a, startIdx, endIdx) == 0.0
	decreases endIdx - startIdx
{}

lemma sum_realNat(a: seq<real>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx <= endIdx <= |a|
	requires forall idx: int | startIdx <= idx < endIdx :: a[idx] >= 0.0
	ensures sum_real(a, startIdx, endIdx) >= 0.0
	decreases endIdx - startIdx
{}

lemma sum_realNatMonotonic(a: seq<real>, startIdx: nat, endIdx: nat, idx: nat)
	requires 0 <= startIdx <= idx <= endIdx <= |a|
	requires forall idx: int | startIdx <= idx < endIdx :: a[idx] >= 0.0
	ensures sum_real(a, startIdx, idx) <= sum_real(a, startIdx, endIdx)
{
	if(idx == startIdx) {
		assert sum_real(a, startIdx, idx) == 0.0;
		sum_realNat(a, startIdx, endIdx);
	} else if(idx == endIdx) {
		assert sum_real(a, startIdx, idx) == sum_real(a, startIdx, endIdx);
	} else {
		sum_realSplit(a, startIdx, endIdx, idx);
		assert sum_real(a, startIdx, idx) + sum_real(a, idx, endIdx) == sum_real(a, startIdx, endIdx);
		sum_realNat(a, idx, endIdx);
	}
}

lemma sum_realDecomposeRight(a: seq<real>, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx < endIdx <= |a|
	ensures sum_real(a, startIdx, endIdx) == sum_real(a, startIdx, endIdx-1) + a[endIdx-1]
{
	calc == {
		sum_real(a, startIdx, endIdx); {sum_realSplit(a, startIdx, endIdx, endIdx-1);}
		sum_real(a, startIdx, endIdx-1) + sum_real(a, endIdx-1, endIdx);
		sum_real(a, startIdx, endIdx-1) + a[endIdx-1];
	}
}

lemma sum_realDif(a: seq<real>, b: seq<real>, difIdx: nat, dif: real, startIdx: nat, endIdx: nat)
	requires 0 <= startIdx < endIdx <= |a|
	requires startIdx <= difIdx < endIdx
	requires |a| == |b|
	requires forall i: nat | i < difIdx :: a[i] == b[i]
	requires forall i: nat | difIdx < i < |a| :: a[i] == b[i]
	requires b[difIdx] == a[difIdx] + dif
	ensures sum_real(b, startIdx, endIdx) == sum_real(a, startIdx, endIdx) + dif
	decreases endIdx - startIdx
{
	if(startIdx == endIdx-1) {
		calc == {
			sum_real(b, startIdx, endIdx);
			b[startIdx];
			b[difIdx];
			a[difIdx] + dif;
			a[startIdx] + dif;
			sum_real(a, startIdx, endIdx) + dif;
		}
	} else if(difIdx == startIdx) {
		calc == {
			sum_real(b, startIdx, endIdx);
			b[startIdx] + sum_real(b, startIdx + 1, endIdx);
			b[difIdx] + sum_real(b, startIdx + 1, endIdx);
			a[difIdx] + dif + sum_real(b, startIdx + 1, endIdx);
			a[startIdx] + dif + sum_real(b, startIdx + 1, endIdx); { sum_realSegmentEqual(a, b, startIdx+1, endIdx); }
			a[startIdx] + dif + sum_real(a, startIdx + 1, endIdx);
			a[startIdx] + sum_real(a, startIdx + 1, endIdx) + dif;
			sum_real(a, startIdx, endIdx) + dif;
		}
	} else {
		sum_realDif(a, b, difIdx, dif, startIdx + 1, endIdx);
		assert sum_real(b, startIdx+1, endIdx) == sum_real(a, startIdx+1, endIdx) + dif;
		calc == {
			sum_real(b, startIdx, endIdx);
			b[startIdx] + sum_real(b, startIdx+1, endIdx);
			b[startIdx] + sum_real(a, startIdx+1, endIdx) + dif;
			a[startIdx] + sum_real(a, startIdx+1, endIdx) + dif;
			sum_real(a, startIdx, endIdx) + dif;
		}
	}
}




ghost function and_seq(a: seq<bool>, startIdx: nat, endIdx: nat): bool
	requires 0 <= startIdx <= endIdx <= |a|
	decreases endIdx - startIdx
{
	if(startIdx == endIdx) then true
	else a[startIdx] && and_seq(a, startIdx + 1, endIdx)
}
