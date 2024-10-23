include "Item.dfy"
include "Especificacion.dfy"
include "Input.dfy"

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

  ghost predicate Valid (input : Input)
    reads this, itemsAssign, input, input.items
  {
    && Model().Valid(input.Model())
    && Model().TotalWeight(input.Model().items) == totalWeight
    && Model().Value(input.Model().items) == totalValue
  }

  ghost function Model() : SolutionData
    reads this, itemsAssign
  {
    SolutionData(itemsAssign[..], k)
  }

  ghost predicate Optimal(input: Input)
    reads this, itemsAssign, input, input.items

    requires this.Valid(input) // yo como solution debo ser válida
    requires input.Valid() // la entrada debe ser valida
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input.Model()) :: otherSolution.Value(input.Model().items) <= this.Model().Value(input.Model().items)
  }

  // es correcto lo de arriba? 




}