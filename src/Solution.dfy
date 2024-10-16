include "Item.dfy"

class Solution {
  var itemsAssign: array<bool> //objetos seleccionados (si o no)
  var totalValue: real
  var totalWeight: real
  var k: int

  constructor(itemsAssign: array<bool>, totalV: real, totalW: real, k': int) {
    this.itemsAssign := itemsAssign;
    this.totalValue := totalV;
    this.totalWeight := totalW;
    this.k := k';
  }

  predicate Valid (items: array<Item> , maxWeight: real)
    reads this
  {
    0 <= this.k <= this.itemsAssign.Length &&
    this.itemsAssign.Length == items.Length &&
    this.totalWeight <= maxWeight
  }



}