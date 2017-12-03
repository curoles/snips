package edc

import edc.Edc.Action

class Wire(simi: edc.Simulation) {

    val sim: edc.Simulation = simi;

    type Level = Boolean

    private var sigVal: Level = false
    private var actions: List[Action] = List()

    def getSignal : Level = sigVal

    def setSignal(newSigVal: Level) : Unit = {
        if (newSigVal != sigVal) {
            sigVal = newSigVal
            actions foreach (_ ())
        }
    }

    def addAction(a: Action) = {
        sim.log("wire add action:" + a.toString)
        actions = a :: actions
        a()
    }
}
