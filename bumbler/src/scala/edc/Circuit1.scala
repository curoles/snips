package edc

class Circuit1(simi: edc.Simulation) {

    val sim: edc.Simulation = simi;

    sim.log("new circuit")

    val reset = new Wire(sim)

    val clk = new Wire(sim)

    Driver.clock(2, clk)
    clk.setSignal(true)
}
