//A nivel de especificación tenemos estos datatype

datatype ItemData = ItemData(weight: real, value: real) {
  ghost predicate Valid() {
    weight > 0.0 && value > 0.0
  }
}

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, totalWeight: real, totalValue: real, k: int) {
  ghost function Valid(itemsD: seq<ItemData>, maxWeight: real) : bool {
    0 <= k <= |itemsAssign| &&
    |itemsAssign| == |itemsD|
    && totalWeight <= maxWeight    
  }

}