include "InputData.dfy"
include "ItemData.dfy"
include "../../ContainersOps.dfy"
include "../../Math.dfy"

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {

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
    && 0 <= k <= |itemsAssign| 
    && |itemsAssign| == |input.items|
    && this.TotalWeight(input.items) <= input.maxWeight
  }

  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input) :: otherSolution.TotalValue(input.items) <= TotalValue(input.items)
  }

  ghost predicate Extends(ps : SolutionData) // ps es prefijo de ps' (el que llama a la función), (ps y ps' iguales hasta k)
    requires |this.itemsAssign| == |ps.itemsAssign|
  { 
    forall i :: 0 <= i < this.k ==> this.itemsAssign[i] == ps.itemsAssign[i]
  }

  ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
    requires ps.Partial(input)
    requires input.Valid()
  {
    && this.Extends(ps)
    && forall s | s.Valid(input) && s.Extends(ps) :: s.TotalValue(input.items) <= this.TotalValue(input.items)
  }
  
}