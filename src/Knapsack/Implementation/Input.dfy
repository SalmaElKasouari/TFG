/*---------------------------------------------------------------------------------------------------------------------

La clase Solution implementa una representación formal la entrada del problema de la mochila.

Estructura del fichero:

  Atributos y constructor

  Predicados
    - Valid: un input es válido.

  Funciones
    - ModelAt: devuelve el modelo del objeto en la posición i del array items.
    - ItemsUntil: devuelve en una secuencia los k primeros elementos (Item) del array items convertidos a ItemData.
    - Model: devuelve el modelo de un Input.
  
  Lemas
    - InputDataItems: el peso y valor de un cierto k en items coinciden con el peso y el valor correspondientes
      en el modelo de items.
    - InputDataItemsForAll: generalización del lema anterior.

---------------------------------------------------------------------------------------------------------------------*/


include "Item.dfy"
include "../Specification/InputData.dfy"

class Input {

  /* Atributos y constructor */
  var items: array<Item>
  var maxWeight: real

  constructor(items: array<Item>, maxWeight: real)
    ensures this.items == items
    ensures this.maxWeight == maxWeight
  {
    this.items := items;
    this.maxWeight := maxWeight;
  }



  /* Predicados */
  /* 
  Predicado: verifica que una entrada sea válida, es decir, que su modelo sea válido.
  */
  ghost predicate Valid()
    reads this, items, set i | 0 <= i < items.Length :: items[i]
  {
    this.Model().Valid()
  }



  /* Funciones */

  /* 
  Función: devuelve el modelo del objeto en la posición i del array items.
  */
  ghost function ModelAt (i : nat) : ItemData
    reads this, items, items[i]
    requires i < items.Length
  {
    items[i].Model()
  }


  /* 
  Función: devuelve en una secuencia los k primeros elementos del array items convertidos a ItemData.
  */
  ghost function ItemsUntil(k: nat): seq<ItemData>
    reads this, items, set i | 0 <= i < k :: items[i]
    requires k <= items.Length
    ensures |ItemsUntil(k)| == k
    ensures forall i | 0 <= i < k :: ItemsUntil(k)[i].weight == this.items[i].weight
    ensures forall i | 0 <= i < k :: ItemsUntil(k)[i].value == this.items[i].value
  {
    if k == 0 then
      []
    else
      ItemsUntil(k-1) + [items[k-1].Model()]
  }


  /* 
  Función: devuelve el modelo de un Input (entrada del problema).
  */
  ghost function Model() : InputData
    reads this, items, set i | 0 <= i < items.Length :: items[i]
    ensures |Model().items| == items.Length
    ensures forall i | 0 <= i < items.Length :: Model().items[i].weight == items[i].weight
    ensures forall i | 0 <= i < items.Length :: Model().items[i].value == items[i].value
  {
    InputData(ItemsUntil(items.Length), maxWeight)
  }



  // /* Métodos */

  // /* 
  // Método: ordena un array de elementos de tipo Item de manera decreciente segun valor por unidad de peso.
  // */
  // method orderItemsByValuePerWeight(items: seq<Item>) returns (orderedItems: seq<Item>)
  //   ensures forall i, j :: 0 <= i < j < |orderedItems| ==>
  //                            orderedItems[i].ValuePerWeight() >= orderedItems[j].ValuePerWeight()
  // {
  //   orderedItems := MergeSort(items[0..]);
  // }

  // method MergeSort(items: seq<Item>) returns (orderedItems : seq<Item>)
  // {
  //   if (|items| > 1) {
  //     var m := |items| / 2;
  //     var izq := MergeSort(items[..m]);
  //     var der := MergeSort(items[m..]);
  //     orderedItems := Merge(izq, der);
  //   }
  // }

  // method Merge(izq: seq<Item>, der: seq<Item>) returns (ordenado : seq<Item>)
  // {    
  //   var i := 0;
  //   var j := 0;

  //   while (i < |izq| && j < |der|)
  //   {
  //     if (izq[i].ValuePerWeight() >= der[j].ValuePerWeight()) {
  //       ordenado := ordenado + [izq[i]];
  //       i := i + 1;
  //     } else {
  //       ordenado := ordenado + [der[j]];
  //       j := j + 1;
  //     }
  //   }
  //   ordenado := ordenado + izq[i..] + der[j..];
  //   //transformar a array
  // }

  // method seqToarray(s: seq<Item>) returns (array<Item>)
  //   ensures |result| == |s|
  // ensures forall i :: 0 <= i < |s| ==> result[i] == s[i]
  // {
  //   var a := new Item[|s|];
  //   for i := 0 to |s| {
  //     a[i] := s[i];
  //   }
  //   return a;
  // }



  /* Lemas */

  /*
  Lema: dada una posición k, el peso y el valor del objeto Item en dicha posición del array items, son iguales al
  peso y el valor correspondientes en el modelo de items. 
  //
  Propósito: demostrar el lema InputDataItemsForAll.
  //
  Verificación: trivial.
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
  Lema: generalización del lema anterior. Establece que para cada item en items, el peso y el valor de ese 
  item coinciden con el peso y el valor correspondientes en el modelo.
  //
  Propósito:
  //
  Verificación:
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
