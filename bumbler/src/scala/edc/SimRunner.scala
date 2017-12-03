package edc

//scala -cp "./build/scala/class:./build/scala/extralib/*" edc.SimRunner

object SimRunner {
    def main(args: Array[String]): Unit = {
        val sim = new edc.Simulation
        val circuit = new edc.Circuit1(sim)
        sim.run
        sys.exit(0)
    }
}
