package core.messages

class MessageLogger:
  private var loggedMessages: List[Message] = Nil

  def log(msg: Message): Unit = loggedMessages = msg :: loggedMessages

  def messages: List[Message] = loggedMessages

