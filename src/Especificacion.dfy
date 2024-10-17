//A nivel de especificación tenemos estos datatype

datatype ItemData = ItemData(weight: real, value: real) {
  ghost predicate Valid() {
    weight > 0.0 && value > 0.0
  }
}

datatype InputData = InputData(itemsD: seq<ItemData>, maxWeight: real)

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, totalWeight: real, totalValue: real, k: int) {
  ghost predicate Valid(input: InputData){
    0 <= k <= |itemsAssign| &&
    |itemsAssign| == |input.itemsD|
    && totalWeight <= input.maxWeight    
  }

}