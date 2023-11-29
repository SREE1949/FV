# Basics
-------------------
*This example shows the FV of FIFO module,which already given in the [SymbiYosys Documentation](https://symbiyosys.readthedocs.io/en/latest/quickstart.html) page* <br>
**.sby**: SymbiYosys (sby) uses a .sby file to define a set of tasks used for verification.(*command: sby fifo.sby*). A .sby file consists of sections [tasks],[options],[engines],[script] and [files]. <br>
*example syntax of a .sby file given below* <br> <br><br>
[tasks]<br>
task_name1 option1 hostA deviceX<br>
task_name2 option2 hostA deviceX<br>

[options]<br>
option1: mode prove  #mode option is mandatory. Possible values are bmc,live,prove,cover<br>
option2: mode live<br>

[engines]<br>
option1: engine_name solver_name  #we mainly use smtbmc engige which support all solvers with bmc,prove and cover modes <br>
option2: engine_name solver_name<br>

[script]<br>
hostA: read -sv hostA.v   #default for read -sv when Yosys is built with Verific support<br>
deviceX: read -sv deviceX.v<br>

[files]<br>
hostA.v<br>
deviceX.v<br>

**For help use below commands**<br>
yosys<br>
help<br>
