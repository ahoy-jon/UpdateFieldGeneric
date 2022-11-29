package io.univalence.stackoverflow



import language.experimental.macros
import magnolia1._

import scala.reflect.ClassTag
import scala.reflect.runtime.universe
import scala.util.Try


case class Transformed[V,W](result: V, warnings: Seq[W]) {
  def map[B](f: V => B):Transformed[B,W] = Transformed(f(result), warnings)
}

sealed trait Path {

  def depth:Int = getParent.map(_.depth +1).getOrElse(0)

  def getParent:Option[Path] =
    this match {
      case Path.Root => None
      case Path.Field(p, _) => Some(p)
      case Path.Optional(p) => Some(p)
      case Path.Sequential(p) => Some(p)
    }
}

object Path {
  case object Root extends Path
  case class Field(parent:Path, name:String) extends Path
  case class Optional(parent:Path) extends Path
  case class Sequential(parent:Path) extends Path
}

object UpdateGeneric {


  class On[X] {
    def updateSome[V:Updater.ToTraverse](value:V):UpdateSome[V] = new UpdateSome[V] {
      override def using[W](tx: (Path, X) => Either[W, X]): Transformed[V, W] = {
        implicitly[Updater.ToTraverse[V]].using(value,tx, Path.Root)
      }
    }

    trait UpdateSome[V] {
        def using[W](tx: (Path, X) => Either[W, X]): Transformed[V,W]
    }


    sealed trait Updater[V]

    trait UpdaterLowPriority2 {
      implicit def toSkip[V]: Updater.ToSkip[V] = new Updater.ToSkip
    }

    trait UpdaterLowPriority1 extends UpdaterLowPriority2 {
      implicit def opt[V](implicit updater: Updater[V]):Updater.ToTraverse[Option[V]] = new Updater.ToTraverse[Option[V]] {
        override def using[W](v: Option[V], tx: (Path, X) => Either[W, X], base:Path): Transformed[Option[V], W] = {
          v match {
            case None => Transformed(None, Nil)
            case Some(vv) =>
              updater match {
                case tt:Updater.ToTraverse[V] => tt.using(vv,tx, Path.Optional(base) ).map(x => Some(x))
                case _ => Transformed(v, Nil)
              }
          }
        }
      }
    }

    object Updater extends UpdaterLowPriority1 {


      implicit case object ToUpdate extends Updater[X]

      class ToSkip[V] extends Updater[V]

      trait ToTraverse[V] extends Updater[V] {
        def using[W](v:V , tx: (Path, X) => Either[W, X], base:Path): Transformed[V,W]
      }

      type Typeclass[T] = Updater[T]

      def join[T](ctx: CaseClass[Typeclass, T]): Updater.ToTraverse[T] = new Updater.ToTraverse[T] {
        override def using[W](v: T, tx: (Path, X) => Either[W, X], base:Path): Transformed[T, W] = {
          val all = ctx.parameters.map(param =>  {
            param.typeclass match {
              case _:ToSkip[_] => Transformed(param.dereference(v), Nil)
              case tt:ToTraverse[param.PType] =>
                tt.using(param.dereference(v), tx, Path.Field(base, param.label))
              case _ =>
                val x = param.dereference(v).asInstanceOf[X]
                val e: Try[Either[W, X]] = scala.util.Try(tx(Path.Field(base, param.label), x)).recover({ case _: MatchError => Right(x) })
                e.get.fold(w => Transformed(x, List(w)), x => Transformed(x, Nil))
            }
          })

          Transformed(ctx.rawConstruct(all.map(_.result))  ,all.flatMap(_.warnings))
        }
      }

      implicit def gen[T]: Updater.ToTraverse[T] = macro Magnolia.gen[T]
    }
  }

  def on[X]:On[X] = new On
}


object UpdateGenericWithReflexion {
  import scala.reflect.runtime.universe._



  class On[X:TypeTag] {


    trait UpdateSome[V] {
      def using[W](tx: (Path, X) => Either[W, X]): Transformed[V,W]
    }


    def updateSome[V:TypeTag](v:V):UpdateSome[V] = new UpdateSome[V] {
      override def using[W](tx: (Path, X) => Either[W, X]): Transformed[V, W] = {

        implicit def typeToClassTag[T: TypeTag]: ClassTag[T] = {
          ClassTag[T]( typeTag[T].mirror.runtimeClass( typeTag[T].tpe ) )
        }

        val valueTag = implicitly[TypeTag[V]]
        val targetType = implicitly[TypeTag[X]]

        val tv: universe.Type = typeOf[V]

        val copy = tv.members.collectFirst({
          case s:MethodSymbol if s.name.toString == "copy" => s
        })

        val mirror = targetType.mirror

        val reflectCopy = mirror.reflect(v).reflectMethod(copy.get.asMethod)

        val constructor = tv.members.collectFirst({
          case s:MethodSymbol if s.isConstructor => s
        })

        val const = mirror.reflectClass(valueTag.tpe.typeSymbol.asClass).reflectConstructor(constructor.get)


        val newV = reflectCopy.apply(None).asInstanceOf[V]


        val newNewV = const(None).asInstanceOf[V]


        valueTag.tpe

        Transformed(newNewV, Nil)
      }
    }

  }


  def on[X:Manifest]:On[X] = new On[X]

}


case class SomeObjectA(toto:Option[String], titi:Int, tata: Option[Int], inner:Option[SomeObjectB])

case class SomeObjectB(tutu:Option[String])


/**
 * Todo
 * * change the order of the DSL UpdateGeneric.On[Option[String].using({case (_, Some("toto")) => Right(None)}).update(v)
 * * try the reflexion based version
 * * check the Path construction
 *
 */
object TestSyntaxManifest {

  private val b: SomeObjectB = SomeObjectB(Some("tutu"))
  val a: SomeObjectA = SomeObjectA(Some("toto"), 0, Some(1), Some(b))

  private val plop: UpdateGenericWithReflexion.On[Option[String]] = UpdateGenericWithReflexion.on[Option[String]]

  val res: Transformed[SomeObjectB, Int] =
    plop.updateSome(b).using[Int]((p, x) => {
      Right(None)
    })


  def main(args: Array[String]): Unit = {
    assert(res.result == b.copy(None))

  }

}

object TestSyntax {

  val a: SomeObjectA = SomeObjectA(Some("toto"), 0, Some(1), Some(SomeObjectB(Some("tutu"))))
  private val opt: UpdateGeneric.On[Option[String]] = UpdateGeneric.on[Option[String]]

  opt.Updater.gen[SomeObjectB]
  opt.Updater.gen[SomeObjectA]


  def main(args: Array[String]): Unit = {
    val a2: SomeObjectA = opt.updateSome(a).using((_,_) => Right(None)).result

    assert(a2 == a.copy(None, inner = a.inner.map(_.copy(None))))

    val result = opt.updateSome(a).using({
      case (path, _) if path.depth < 2 => Right(None)
    }).result


    assert(result == a.copy(None))

  }



}





