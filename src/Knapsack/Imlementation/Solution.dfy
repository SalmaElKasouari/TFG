include "Item.dfy"
include "../Specification/SolutionData.dfy"
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

  ghost predicate ValidateElements(input : Input) //pongo esta función porque es comun para Valid y Partial
    reads this, itemsAssign, input, input.items
  {
    && Model().Valid(input.Model())
    && Model().TotalWeight(input.Model().items) == totalWeight
    && Model().TotalValue(input.Model().items) == totalValue
  }

  ghost predicate Partial (input : Input)
    reads this, itemsAssign, input, input.items
  {
    && 0 <= this.k < this.itemsAssign.Length
    && ValidateElements(input)
  }

  ghost predicate Valid (input : Input) // solución completa (final)
    reads this, itemsAssign, input, input.items
  {
    && this.k == this.itemsAssign.Length
    && ValidateElements(input)
  }

  ghost function Model() : SolutionData
    reads this, itemsAssign
  {
    SolutionData(itemsAssign[..], k)
  }

  ghost predicate Optimal(input: Input)
    reads this, itemsAssign, input, input.items

    requires this.Valid(input)  // que la solución que llama al predicado sea completa --> valid
    requires input.Valid() // la entrada debe ser valida
  {
    this.Model().Optimal(input.Model())
  }

  ghost function Bound() : int
    reads this
  {
    this.itemsAssign.Length - this.k + 1
  }




}