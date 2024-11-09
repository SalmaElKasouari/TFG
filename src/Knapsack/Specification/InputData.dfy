include "ItemData.dfy"

datatype InputData = InputData(items: seq<ItemData>, maxWeight: real) {
  ghost predicate Valid() {
    && (forall i | 0 <= i < |items| :: items[i].Valid())
    && maxWeight >= 0.0
  }
}