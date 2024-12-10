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



  /*ghost function Model() : InputData
    reads this, items, set i | 0 <= i < items.Length :: items[i]
  {
    InputData(seq(items.Length, ModelAt), maxWeight)
  }*/


  ghost function ItemsUntil(k: nat): seq<ItemData>
    reads this, items, set i | 0 <= i < k :: items[i]
    requires k <= items.Length
    ensures |ItemsUntil(k)| == k
    ensures forall i | 0 <= i < k :: ItemsUntil(k)[i].weight == items[i].weight
    ensures forall i | 0 <= i < k :: ItemsUntil(k)[i].value == items[i].value
  {
    if k == 0 then
      []
    else
      ItemsUntil(k-1) + [items[k-1].Model()]
  }

  ghost function Model() : InputData
    reads this, items, set i | 0 <= i < items.Length :: items[i]
    ensures |Model().items| == items.Length
    ensures forall i | 0 <= i < items.Length :: Model().items[i].weight == items[i].weight
    ensures forall i | 0 <= i < items.Length :: Model().items[i].value == items[i].value
  {
    InputData(ItemsUntil(items.Length), maxWeight)
  }


  ghost predicate Valid()
    reads this, items, set i | 0 <= i < items.Length :: items[i] //añadido esto ultimo, era necesario también
  {
    this.Model().Valid()
  }

   lemma InputDataItems(k:int)
  requires 0 <= k < items.Length
  ensures items[k].weight == Model().items[k].weight
  ensures items[k].value == Model().items[k].value
  {}
}
