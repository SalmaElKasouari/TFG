include "Item.dfy"
include "Especificacion.dfy"

class Solution {
  var itemsAssign: array<bool> //objetos seleccionados (si o no)
  var totalValue: real
  var totalWeight: real
  var k: nat

  constructor(itemsAssign: array<bool>, totalV: real, totalW: real, k': nat) {
    this.itemsAssign := itemsAssign;
    this.totalValue := totalV;
    this.totalWeight := totalW;
    this.k := k';
  }

  ghost predicate Valid (input : InputData)
    reads this, itemsAssign
  {
    && Model().Valid(input) 
    && Model().TotalWeight(input.items) == totalWeight
    && Model().SolutionValue(input.items) == totalValue
  }

  ghost function Model() : SolutionData 
  reads this, itemsAssign
  {
    SolutionData(itemsAssign[..], k)
  }



}