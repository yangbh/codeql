private import java
// private import DataFlowPrivate
// private import semmle.code.java.dataflow.SSA
// private import semmle.code.java.controlflow.Guards
private import semmle.code.java.dataflow.ExternalFlow
private import semmle.code.java.dataflow.FlowSteps
private import semmle.code.java.dataflow.FlowSummary
private import semmle.code.java.dataflow.InstanceAccess
private import FlowSummaryImpl as FlowSummaryImpl
private import TaintTrackingUtil as TaintTrackingUtil
private import DataFlowNodes
import DataFlowNodes::Public

/** Value step from the constructor call of a `Runnable` to the instance parameter (this) of `run`. 
 * 
 * Class MyRunnable implements Runnable{
 *    public void run(){}
 * }
 * MyRunnable m = new MyRunnable(xxx)
 * additional step:
 * from:  new MyRunnable(xxx)
 * to:    MyRunnable#run#this
*/ 
private class RunnableStartToRunStep extends AdditionalValueStep {
  override predicate step(Node pred, Node succ) {
    exists(ConstructorCall cc, Method m |
      (
        m.getDeclaringType() = cc.getConstructedType().getSourceDeclaration()
        or 
        m.getDeclaringType() = cc.getConstructedType().getASupertype() 
        and cc.getConstructedType().toString().matches("new%{%}")
      ) 
      // m.getDeclaringType() = cc.getConstructedType().getSourceDeclaration() 
      and cc.getConstructedType().getAnAncestor().hasQualifiedName("java.lang", "Runnable") 
      and m.hasName("run")
    |
      pred.asExpr() = cc 
      and succ.(InstanceParameterNode).getEnclosingCallable() = m
      and not pred.getLocation().getFile().getAbsolutePath().matches("%test/src%")
      and not succ.getLocation().getFile().getAbsolutePath().matches("%test/src%")
      // and pred.getLocation().getFile().getAbsolutePath().matches("%FilterServerManager.java")
    )
  }
}
  
// private predicate test(ConstructorCall cc, Method m, RefType t, RefType t2) {
//   (
//     m.getDeclaringType() = cc.getConstructedType().getSourceDeclaration()
//     or 
//     m.getDeclaringType() = cc.getConstructedType().getASupertype() 
//     and cc.getConstructedType().toString().matches("new%{%}")
//   ) 
//   and m.hasName("run")
//   and cc.getConstructedType().getAnAncestor().hasQualifiedName("java.lang", "Runnable")
//   and cc.getLocation().getFile().getAbsolutePath().matches("%FilterServerManager.java")
//   and m.getLocation().getFile().getAbsolutePath().matches("%AbstractBrokerRunnable.java")
//   and t = m.getDeclaringType()
//   and t2 = cc.getConstructedType().getSourceDeclaration()
// }
  
/** 
 * Class RunnableDemo implements Runnable {
 *  public void run(){
 *    ...
 *  }
 * }
 * RunnableDemo T1 = new RunnableDemo(tt);
 * Thread t = new Thread(T1);
 * 
 * additional step:
 * from:  new Thread(T1)
 * to:    RunnableDemo#run#this
 */
private class RunnableStartToRunStep2 extends AdditionalValueStep {
  override predicate step(Node pred, Node succ) {
    exists(ConstructorCall cc, Method m, Argument arg |
      cc.getConstructedType().getAnAncestor().hasQualifiedName("java.lang", "Thread") and
      cc.getArgument(0) = arg and 
      m.getDeclaringType() = arg.getType().(RefType).getSourceDeclaration() and
      m.getDeclaringType().getASourceSupertype().hasQualifiedName("java.lang", "Runnable") and
      m.hasName("run")
    |
      pred.asExpr() = arg 
      and succ.(InstanceParameterNode).getEnclosingCallable() = m
      and not pred.getLocation().getFile().getAbsolutePath().matches("%test/src%")
      and not succ.getLocation().getFile().getAbsolutePath().matches("%test/src%")
    )
  }
}

// private class RunnableStartToRunStep3 extends AdditionalValueStep {
//   override predicate step(Node pred, Node succ) {
//     exists(ConstructorCall cc, Method m |
//       (
//         m.getDeclaringType() = cc.getConstructedType().getSourceDeclaration()
//         or 
//         m.getDeclaringType() = cc.getConstructedType().getASupertype() 
//         and cc.getConstructedType().toString().matches("new%{%}")
//       ) 
//       and cc.getConstructedType().getAnAncestor().hasQualifiedName("java.lang", "Runnable") 
//       and m.hasName("run")
//     |
//       succ.asExpr() = cc.getAnArgument() 
//       and (simpleLocalFlowStep0(pred, succ)
//         or simpleLocalFlowStep0(succ, pred)
//       )
//       and not pred.getLocation().getFile().getAbsolutePath().matches("%test/src%")
//       and not succ.getLocation().getFile().getAbsolutePath().matches("%test/src%")
//       // and pred.getLocation().getFile().getAbsolutePath().matches("%FilterServerManager.java")
//     )
//   }
// }

// /**
//  * func: 内部类构造，由外部内传播至内部类
//  * 内部类实例化
//  * OutClass.InnerClass obj = outClassInstance.new InnerClass(); 
//  * todo: 静态内部类
//  * AAA.StaticInner in = new AAA.StaticInner();
//  */
// private class InnerClassConstrctor2Obj extends AdditionalValueStep {
//   override predicate step(Node pred, Node succ) {
//     exists(ConstructorCall cc|
//       cc.getQualifier() = pred.asExpr()
//       and succ.asExpr() = cc
//     )
//   }
// }

// /**
//  * func: 内部类调用外部类方法
//  * OuterClass{
//  *  InnerClass{
//  *    InnerCall(){
//  *      OuterClass.this.OuterCall();
//  *    }
//  *  }
//  * }
//  */
// private class InnerClassCallOuter extends AdditionalValueStep {
//   override predicate step(Node pred, Node succ) {
//     exists(MethodAccess ma, Method m, InnerClass ic|
//       ma.getMethod() = m
//       and ic = ma.getEnclosingCallable().getDeclaringType()
//       |
//       pred.(InstanceParameterNode).getCallable() = ma.getEnclosingCallable()
//       and succ.(InstanceParameterNode).getCallable() = m
//     )
//   }
// }

private predicate callEdge(Callable c1, Callable c2) {
  exists(Call c | c.getCaller() = c1 and c2 = c.getCallee())
  // for java thread
  or callEdgeInter4Runnable(c1, c2)
  // interface
  or callEdge4Interface(c1, c2)
}

private predicate callEdge4Interface(Callable c1, Callable c2){
  c1.isAbstract()
  and c1 = c2.(Method).getAnOverride()
  and c1 != c2
  and beSourceFile(c2.getFile())
}

private predicate callEdgeInter4Runnable(Callable c1, Callable c2){
  exists(ConstructorCall c | 
    // for java thread
    c1 = c.getCaller()
    and c1.getDeclaringType().getASupertype*().hasQualifiedName("java.lang", "Runnable")
    and c2.hasName("run")
    and (
        c2.getDeclaringType() = c.getConstructedType().getSourceDeclaration()
        or 
        c2.getDeclaringType() = c.getConstructedType().getASupertype() 
        and c.getConstructedType().toString().matches("new%{%}")
    ) 
  )
}

private predicate beSourceFile(File m){
  not m.getFile().getAbsolutePath().matches("/modules/java.base/%")
  and not m.getFile().getAbsolutePath().matches("%.jar/%")
  and not m.getFile().getAbsolutePath().matches("%/src/test/%")
}


private class InnerOuterCall extends Call{
  InnerClass innerClass;
  Class outerClass;

  InnerOuterCall() {
      this.getEnclosingCallable().getDeclaringType() = innerClass
      and this.getCallee().getDeclaringType() = innerClass.getEnclosingType()
      and outerClass = innerClass.getEnclosingType()
  }

  InnerClass getInnerClass() {
      result = innerClass
  }

  Class getOuterClass(){
      result = outerClass
  }
}

private Callable walkOuterCall(Callable c, RefType r){
  exists(Callable t|
      callEdge(c, t) and
      if exists(InnerOuterCall ioa| 
        ioa.getEnclosingCallable() = t
        and ioa.getInnerClass() = r
      ) 
      then result = t
      else result = walkOuterCall(t, r)
      // and result = t
  )
}

private Callable getOuterCall(Callable c){
  exists( InnerOuterCall ioa| ioa.getEnclosingCallable() = c | 
      result = ioa.getCallee()
  )
}

/** 
 * func: patch内部类调用外部类时，无法跟踪进外部类方法
 * done: 
 *  1. 普通内部类
 *  2. 匿名内部类  
 * todo: 
 *  1. 静内部态类
 *  2. 起点是cc.getEnclosingCallable()，可能存在漏的
 */
private class InnerClassConstructorOuter extends AdditionalValueStep {
  override predicate step(Node pred, Node succ) {
    exists(ConstructorCall cc, Constructor c, InnerClass ic, Callable outerCall, Callable target|
      cc.getConstructor() = c
      and ic = c.getDeclaringType()
      and outerCall = walkOuterCall(cc.getEnclosingCallable(), ic)
      and target = getOuterCall(outerCall)
      and succ.(InstanceParameterNode).getCallable() = target
      and (
        // 非匿名
        // InnerClass innerClass = outerClass.new InnerClass();
        not ic instanceof AnonymousClass
        and pred.asExpr() = cc.getQualifier()
        // 匿名
        // func(new InnerClass(){})
        or ic instanceof AnonymousClass
        and pred.(InstanceParameterNode).getCallable() = cc.getEnclosingCallable()
      )
    )
  }
}

predicate test(ConstructorCall cc, Constructor c, InnerClass ic
  , Callable outerCall
  , Callable target
  , Node pred
  , Node succ
  ){
    cc.getConstructor() = c
    and ic = c.getDeclaringType()
    and outerCall = walkOuterCall(cc.getEnclosingCallable(), ic)
    and target = getOuterCall(outerCall)
    and succ.(InstanceParameterNode).getCallable() = target
    and (
      // 非匿名
      // InnerClass innerClass = outerClass.new InnerClass();
      not ic instanceof AnonymousClass
      and pred.asExpr() = cc.getQualifier()
      // 匿名
      // func(new InnerClass(){})
      or ic instanceof AnonymousClass
      and pred.(InstanceParameterNode).getCallable() = cc.getEnclosingCallable()
    )
}