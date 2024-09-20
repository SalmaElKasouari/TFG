include "InputData.dfy"

class Solution {
    var objectsSelected: array<bool>
    var maxWeight: real
    var totalValue: real
    var totalWeight: real
    var k: int 

    constructor(objSel: array<bool>, maxW: real, totalV: real, totalW: real, k': int) {
        this.objectsSelected := objSel;
        this.maxWeight := maxW;
        this.totalValue := totalV;
        this.totalWeight := totalW;
        this.k := k';
    }


    /*
        Implementación del ValidSolution: dada una solución cadidata, comprueba si la suma total de los pesos 
        de los objetos seleccionados no supere el peso máximo permitido.
    */
    method ValidSolution(objects: array<InputData>, objEndIdx: nat, maxWeight: real, areSelected: array<bool>) returns (valid: bool)
        requires objEndIdx <= objects.Length
        requires objEndIdx <= areSelected.Length
    { 
        var totalWeight := 0.0;
        for i := 0 to objEndIdx {
            if (areSelected[i]) {
                totalWeight := totalWeight + objects[i].weight; 
            }
        }

        valid := totalWeight <= maxWeight; 
    }

    
}