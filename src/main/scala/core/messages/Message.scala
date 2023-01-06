package core.messages

import core.Context

abstract class Message:
  def level: Message.Level = Message.Level.Error
  def show(using Context): String

object Message:
  enum Level:
    case Error
    case Warning
    case Info

