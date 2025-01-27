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

  /*
  Este lema establece que el peso y valor de un cierto k en items coinciden con el peso y el valor correspondientes
  en el modelo de items. Se utiliza para demostrar el lema InputDataItemsForAll.
  */
  lemma InputDataItems(k : int)
    requires 0 <= k < items.Length
    ensures items[k].weight == Model().items[k].weight
    ensures items[k].value == Model().items[k].value
  {
    assert Model().items[k].weight == items[k].weight;
    assert Model().items[k].value == items[k].value;
  }

  /*
  Este lema es una genrealización del lema anterior. Establece que para cada item en items, el peso y el valor de ese 
  item coinciden con el peso y el valor correspondientes en el modelo.
  */
  lemma InputDataItemsForAll()
    ensures forall k | 0 <= k < items.Length ::
              items[k].weight == Model().items[k].weight &&
              items[k].value == Model().items[k].value
  {
    var n := items.Length;

    if n == 0 {
      assert forall k | 0 <= k < items.Length ::
          items[k].weight == Model().items[k].weight &&
          items[k].value == Model().items[k].value;
    }
    else {
      forall k | 0 <= k < items.Length
        ensures items[k].weight == Model().items[k].weight &&
                items[k].value == Model().items[k].value
      {
        InputDataItems(k);
      }
    }
  }


}
