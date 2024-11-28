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

  ghost function ModelAt (i : nat) : ItemData
    reads this, items, items[i]
    requires i < items.Length
  {
    items[i].Model()
  }

  ghost function Model() : InputData
    reads this, items, set i | 0 <= i < items.Length :: items[i]
  {
    InputData(seq(items.Length, ModelAt), maxWeight)
  }

  ghost predicate Valid()
    reads this, items, set i | 0 <= i < items.Length :: items[i] //añadido esto ultimo, era necesario también
  {
    this.Model().Valid()
  }
}
