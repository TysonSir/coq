## 前言 (**Preface**)
发现新大陆，提升软件质量的第三类方法：
1. 软件项目管理，优化开发流程（如极限编程，Extreme Programming），到库的设计原理（如模型-视图-控制器，Model-View-Controller；发布-订阅模式， Publish-Subscribe）
2. 先进的编程语言设计（面向对象编程，Object Oriented Programmin； 面向剖面编程，Aspect Oriented Programming；函数式编程，Functional Programming）
3.  **用于阐明和论证软件性质的数学技术，以及验证这些性质的工具。**

## Coq 函数式编程 (**Basics**)
函数式编程的特点：**函数式编程关心数据的映射，命令式编程关心解决问题的步骤。**

## 疑惑
**problem.v 中以代码的形式展示**  
	   (* 为何取反的符号不能定义? negb函数已定义，但报错： *)
	   (* The reference x was not found in the current environment. *)
	   Notation  "!x" := (negb x).

> Written with [StackEdit](https://stackedit.io/).

