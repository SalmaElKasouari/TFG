include "Item.dfy"
include "../Specification/InputData.dfy"

class Input {
  var items: array<Item>
  var maxWeight: real

  constructor(items: array<Item>, maxWeight: real) 
    ensures this.items == items
    ensures this.maxWeight == maxWeight
  {
    this.items := items;
    this.maxWeight := maxWeight;
  }

  ghost function Model() : InputData
    reads this, items
  {
    InputData(seq(items.Length, i reads this, items requires 0 <= i < items.Length  => items[i].Model()), maxWeight)
  }

  ghost predicate Valid()
    reads this, items
  {
    this.Model().Valid()
  }
}
