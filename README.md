# Query-Optimiser-for-SJDB
Database Programming Exercise


## 可优化的思路


* （1）子句局部优化。
如等价谓词重写，WHERE和HAVING条件化简中的大部分情况。

* （2）子句间关联优化。
子句与子句之间关联的语义存在优化的可能，如外连接消除、连接消除、子查询优化、视图重写等。

* （3）局部与整体的优化。
协同局部与整体。如OR重写并集规则需要考虑UNION操作（UNION是变换后的整体形式）的花费和OR操作（OR是局部表达式）的花费。

* （4）形式变化优化
多个子句存在嵌套，可能通过形式的变化完成优化。如：嵌套连接消除。

* （5）语义优化
根据完整性约束，SQL表达的含义等信息对语句进行语义优化

* （6）其他优化
根据一些规则对非SPJ做的其他优化，根据硬件环境进行的并行查询优化。

* 它们都是依据关系代数和启发式规则进行。

