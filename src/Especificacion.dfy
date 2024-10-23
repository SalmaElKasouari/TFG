include "ContainersOps.dfy"
include "Math.dfy"
//A nivel de especificación tenemos estos datatype

datatype ItemData = ItemData(weight: real, value: real) {
  ghost predicate Valid() {
    weight > 0.0 && value > 0.0
  }
}

datatype InputData = InputData(items: seq<ItemData>, maxWeight: real) {
  ghost predicate Valid() {
    (forall i | 0 <= i < |items| :: items[i].Valid()) &&
    maxWeight >= 0.0
  }
}

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

  ghost function Value(items: seq<ItemData>): (o: real)
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    var objSelected: seq<ItemData> := selectSeq(items, itemsAssign, 0, k);
    var numSelected: nat := |objSelected|;
    var valuesSelected: seq<real> := mapSeq(objSelected, (obj: ItemData) => obj.value, 0, numSelected);
    sum_real(valuesSelected, 0, numSelected)
  }

  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input) :: otherSolution.Value(input.items) <= Value(input.items)
  }

  ghost predicate Valid(input: InputData){
    0 <= k <= |itemsAssign| &&
    |itemsAssign| == |input.items|
    && this.TotalWeight(input.items) <= input.maxWeight
  }

}