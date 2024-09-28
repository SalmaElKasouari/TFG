include "InputData.dfy"

class Solution {
    var objects: array<InputData> //objetos (valor, peso)
    var objectsAssign: array<bool> //objetos seleccionados (si o no)
    var maxWeight: real
    var totalValue: real
    var totalWeight: real
    var k: int

    constructor(objects: array<InputData>, objectsAssign: array<bool>, maxW: real, totalV: real, totalW: real, k': int) {
        this.objects := objects;
        this.objectsAssign := objectsAssign;
        this.maxWeight := maxW;
        this.totalValue := totalV;
        this.totalWeight := totalW;
        this.k := k';
    }

    predicate ValidSolution ()  
        reads this
    {
        this.totalWeight <= this.maxWeight 
    }


    /*
        Implementación del ValidSolution: dada una solución cadidata, comprueba si la suma total de los pesos 
        de los objetos seleccionados no supere el peso máximo permitido.
    */
    // method ValidSolution(objects: array<InputData>, objEndIdx: nat, maxWeight: real, objectsAssign: array<bool>) returns (valid: bool)
    //     requires objEndIdx <= objects.Length
    //     requires objEndIdx <= objectsAssign.Length
    // { 
    //     var totalWeight := 0.0;
    //     for i := 0 to objEndIdx {
    //         if (objectsAssign[i]) {
    //             totalWeight := totalWeight + objects[i].weight; 
    //         }
    //     }

    //     valid := totalWeight <= maxWeight; 
    // }

  
   
}