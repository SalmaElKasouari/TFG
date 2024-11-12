include "Item.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

class Solution {
  var itemsAssign: array<bool> //objetos seleccionados (si o no)
  var totalValue: real
  var totalWeight: real
  var k: nat

  constructor(itemsAssign: array<bool>, totalV: real, totalW: real, k': nat) 
    //constructor con nombre requires campo a campo 
    ensures itemsAssign == this.itemsAssign
    ensures this.totalValue == totalV
    ensures this.totalWeight == totalW
    ensures this.k == k'

  {
    this.itemsAssign := itemsAssign;
    this.totalValue := totalV;
    this.totalWeight := totalW;
    this.k := k';
  }

  
 
  ghost predicate Partial (input : Input)
    reads this, this.itemsAssign, input, input.items
  {    
    && 0 <= this.k <= this.itemsAssign.Length
    && Model().Partial(input.Model())
    && Model().TotalWeight(input.Model().items) == totalWeight
    && Model().TotalValue(input.Model().items) == totalValue
  }

  ghost predicate Valid (input : Input) // solución completa (final)
    reads this, this.itemsAssign, input, input.items
  {
    && this.k == this.itemsAssign.Length
    && Partial(input)
  }

  ghost function Model() : SolutionData
    reads this, itemsAssign
  {
    SolutionData(itemsAssign[..], k)
  }

  ghost predicate Optimal(input: Input)
    reads this, this.itemsAssign, input, input.items

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

  ghost predicate Extends(ps : Solution)
    reads this, this.itemsAssign, ps, ps.itemsAssign

    requires this.itemsAssign.Length == ps.itemsAssign.Length
    requires this.k <= this.itemsAssign.Length   
    requires ps.k <= this.k
  {
    this.Model().Extends(ps.Model())
  }

  ghost predicate OptimalExtension(ps : Solution, input : Input)
    reads this, this.itemsAssign, ps, ps.itemsAssign, input, input.items
    
    requires input.Valid()
  {
    this.Model().OptimalExtension(ps.Model(), input.Model())
  }

  ghost predicate equalsSolutions(ps : Solution)
    reads this, this.itemsAssign, ps, ps.itemsAssign

    requires this.itemsAssign.Length == ps.itemsAssign.Length
    requires this.k <= this.itemsAssign.Length
    requires ps.k <= ps.itemsAssign.Length
    requires ps.k == this.k   
  {
    this.Model().equals(ps.Model())
  }


}