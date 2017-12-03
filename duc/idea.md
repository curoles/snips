Original idea March 2014
========================

DUC stays for Design Under Cover.

Main idea behind DUC: a tool that “just works”, initially no work from DV engineers is required,
later on DV team can improve DUC’s feedback by providing more information.

DUC works in background, you run a test, the run is reported to DUC engine,
DUC engine visits run’s directory and collects information.

Design or DUT – all RTL source code files that constitute product.

Cluster – set of source code files for a certain part or subset of Design,
cluster could be simulated as a unit/module with corresponding cluster TB(s).

Test – a program that defines test inputs and checks outputs, to be executed by TB.

Run – RTL simulation of test.

In order to find out coverage we need to know: a) coverage space and b) what part of coverage space was covered in a run.

All source code files fall into 2 categories: DUT files and TB files.

Coverage space:
1. auto-detection: lines of code, assertions;
2. information: DUT files, TB files, IP spec, functional partitions, test metrics.

All test metrics are orthogonal. DUC plugin for each metric.

Metrics:
- Visited lines of code
- Visited assertions
- Test pass/failure
 
Some modules might have well known nature, that nature can suggest verification methods:
1. Register
2. Bus interface
3. State machine
4. Muxes , Encoders and Decoders
5. FIFO (was filled, emptied)
6. Interrupt Generation, DMA
7. Reset
8. Communication channel, interface: transmitted all packet types across the channel; transmitted all packet types.

DUC DB collects metrics, saves # of hits, age, DUT revision, host machine, user name.

References:
http://www.design-reuse.com/articles/18353/assertion-based-formal-verification.html
http://www.eetimes.com/document.asp?doc_id=1217979
http://network.ku.edu.tr/~stasiran/publications/d4tasi.lo.pdf
http://www.cs.huji.ac.il/~ornak/publications/charme03a.pdf
http://my.safaribooksonline.com/book/electrical-engineering/semiconductor-technology/0131433474
https://smiweb.smi.local/wiki/display/DV/DV+Methodology

