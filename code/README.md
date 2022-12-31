## AI 大作业

### 目录结构说明

+ SAT.py：主要的实现文件，实现了CDCL的整体框架，内部实现了SAT类
+ solver.py：main文件，读取命令行参数并实例化SAT对象，调用SAT.solve()方法解决sat问题，并对结果进行验证
+ decider.py：实现了Decider类，在SAT中被实例化
+ restarter.py：实现了Restarter类，在SAT中被实例化
+ utils.py：实现了一些辅助类，包括Statistics（用于统计运行数据），PriorityQueue（优先级队列，用于decider中），LubyGenerator（生成LUBY序列），Test（对结果进行测试）



### 测试方式

进入`code/`目录，使用如下命令进行测试：

~~~shell
python ./solver.py -i <input_file_path> -d <decider> -r <restarter> -b <BVE_flag> -t <Test_flag> --base <restarter base>
~~~

`solver.py `文件接收六个参数：

+ `'-i','--input'`：输入的测试文件保存路径
+ `'-d','--decider'`：初始化decider的heuristic方式，可以是`["VSIDS","LRB","CHB"]`其中之一，默认参数为`"VSIDS"`
+ `'-r','--restarter'`：restarter的内部restart方式，可以是`["GEOMETRIC","LUBY","NO_RESTART"]`其中之一，默认参数为`"LUBY"`
+ `'-b','--bve'`：是否使用BVE来进行预处理的标志参数，可以是`[“True”,"False"]`其中之一，默认参数为`"False"`
+ `'-t','--test'`：是否进行测试的标志参数，可以是`[“True”,"False"]`其中之一，默认参数为`"True"`
+ `--base'`：restarter内部的restart base，用于生成对应的conflict limit序列，可以是一个int，默认参数为`"1024"`



测试时间根据测试文件的复杂程度和所选的参数等有较大的差异，bmc-1.cnf测试文件大概可以在20s左右完成。

我们的代码会在当前目录中建立一个Results/目录储存测试结果，分别是一份赋值的结果以及一份统计数据，分别以`assgn_xxx.txt`和`stats_xxx.txt`命名。


