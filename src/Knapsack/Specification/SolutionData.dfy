include "InputData.dfy"
include "ItemData.dfy"
include "../../ContainersOps.dfy"
include "../../Math.dfy"

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {
  
  static lemma {:induction} selectSeqFalses<T>(a :seq<T>, b : seq<bool>, startIdx : nat, endIdx : nat) 
    decreases endIdx - startIdx
    requires 0 <= startIdx <= endIdx <= |a| 
    requires endIdx <= |b|
    requires forall i | 0 <= i < |b| :: !b[i]
    ensures selectSeq(a, b, startIdx, endIdx) == []
  {  
    if startIdx == endIdx { //Base
      assert true;
    } 
    else if b[startIdx] { // Esto nunca se alcanza porque todos son falsos (precondición)
      assert false;
    }
    else {
      selectSeqFalses(a, b, startIdx + 1, endIdx);
    }
  }

  lemma SumOfFalsesEqualsZero(input : InputData)
    requires k <= |itemsAssign|
    requires |itemsAssign| == |input.items|
    requires forall i | 0 <= i < |itemsAssign| :: !itemsAssign[i]
    ensures TotalWeight(input.items) == 0.0 && TotalValue(input.items) == 0.0
  {
    // Si ningun objeto ha sido seleccionado (todos asignados a false --> array objetos seleccionado es vacio), la suma total de los pesos/valores de los objetos escogidos (ninguno) es 0:
      assert selectSeq(input.items, itemsAssign, 0, k) == [] by {
        selectSeqFalses(input.items, itemsAssign, 0, k);
      }
  }

  lemma RemoveComponentMaintainsWeightSum(items: seq<ItemData>)
    requires k <= |items|
    requires k <= |itemsAssign|
    requires |itemsAssign| == |items|
    ensures TotalWeight(selectSeq(items, itemsAssign, 0, |items|)) ==
            TotalWeight(selectSeq(items, itemsAssign, 0, |items| - 1)) + items[|items| - 1].weight

{
  //demo
}

lemma AddFalsePreservesWeight(input: InputData, itemsAssign: seq<bool>)
    requires k < |itemsAssign| && k < |input.items|
    requires |itemsAssign| == |input.items|
    requires itemsAssign[k] == false
    ensures TotalWeight(selectSeq(input.items, itemsAssign, 0, k + 1)) ==
            TotalWeight(selectSeq(input.items, itemsAssign, 0, k))
{
  //demo
}

  ghost function TotalWeight(items: seq<ItemData>): real
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    var objSelected: seq<ItemData> := selectSeq(items, itemsAssign, 0, k);
    var numSelected: nat := |objSelected|;
    var weightsSelected: seq<real> := mapSeq(objSelected, (obj: ItemData) => obj.weight, 0, numSelected);
    sum_real(weightsSelected, 0, numSelected)
  }

  ghost function TotalValue(items: seq<ItemData>): (o: real)
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    var objSelected: seq<ItemData> := selectSeq(items, itemsAssign, 0, k);
    var numSelected: nat := |objSelected|;
    var valuesSelected: seq<real> := mapSeq(objSelected, (obj: ItemData) => obj.value, 0, numSelected);
    sum_real(valuesSelected, 0, numSelected)
  }

  ghost predicate Partial (input: InputData){
    && 0 <= k <= |itemsAssign| 
    && |itemsAssign| == |input.items|
    && this.TotalWeight(input.items) <= input.maxWeight
  }

  ghost predicate Valid(input: InputData){
    && k == |itemsAssign| 
    && Partial(input)
  }

  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input) :: otherSolution.TotalValue(input.items) <= TotalValue(input.items)
  }

  ghost predicate Extends(ps : SolutionData) // ps es prefijo de ps' (el que llama a la función), (ps y ps' iguales hasta k)
    requires |this.itemsAssign| == |ps.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires ps.k <= this.k 
  { 
    forall i | 0 <= i < ps.k :: this.itemsAssign[i] == ps.itemsAssign[i]
  }

  ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
    requires input.Valid()  
  {
    && this.Valid(input)
    && ps.Partial(input) 
    && this.Extends(ps)
    && forall s : SolutionData | s.Valid(input) && s.Extends(ps) :: s.TotalValue(input.items) <= this.TotalValue(input.items)
  }

  ghost predicate equals(s : SolutionData)
    requires |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign| 
  { 
    && this.k == s.k
    && forall i | 0 <= i < this.k :: this.itemsAssign[i] == s.itemsAssign[i]
  }
  
}