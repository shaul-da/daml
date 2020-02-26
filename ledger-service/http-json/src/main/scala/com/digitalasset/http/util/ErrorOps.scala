// Copyright (c) 2020 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.http.util

import com.digitalasset.util.ExceptionOps
import scalaz.syntax.show._
import scalaz.{Show, \/}

object ErrorOps {

  implicit final class `\\/ WSS extras throwable`[R](private val self: Throwable \/ R)
      extends AnyVal {
    def liftErr[M](f: String => M): M \/ R =
      self leftMap (e => f(ExceptionOps.getDescription(e)))
  }

  implicit final class `\\/ WSS extras`[L, R](private val self: L \/ R) extends AnyVal {
    def liftErr[M](f: String => M)(implicit L: Show[L]): M \/ R =
      self leftMap (e => f(e.shows))

    def liftErrS[M](msg: String)(f: String => M)(implicit L: Show[L]): M \/ R =
      liftErr(x => f(msg + " " + x))
  }
}
