include "Item.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

class Solution {
  var itemsAssign: array<bool> //objetos seleccionados (si o no)
  var totalValue: real
  var totalWeight: real
  var k: nat

  constructor(itemsAssign: array<bool>, totalV: real, totalW: real, k': nat) 
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
    reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
  {    
    && 0 <= this.k <= this.itemsAssign.Length
    && Model().Partial(input.Model())
    && Model().TotalWeight(input.Model().items) == totalWeight
    && Model().TotalValue(input.Model().items) == totalValue
  }

  ghost predicate Valid (input : Input) // solución completa (final)
    reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
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
    reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]

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

  method Copy(s : Solution) 
    modifies this`totalValue, this`totalWeight, this`k
    requires this.k == this.itemsAssign.Length
    requires s.k == s.itemsAssign.Length
    requires this.itemsAssign.Length == s.itemsAssign.Length
    
    ensures this.totalValue == s.totalValue
    ensures this.totalWeight == s.totalWeight
    ensures this.k == s.k
    //ensures forall i | 0 <= i < this.itemsAssign.Length :: this.itemsAssign[i] == s.itemsAssign[i]
  {
    this.totalValue := s.totalValue;
    this.totalWeight := s.totalWeight;
    this.k := s.k;
    // Copiar los elementos del array uno por uno
    // for i := 0 to s.itemsAssign.Length - 1 {
    //   this.itemsAssign[i] := s.itemsAssign[i];
    // }
  }
  


}