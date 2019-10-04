package com.daml.ledger.rxjava.components;

import com.daml.ledger.javaapi.data.*;
import java.util.List;

public class TemplateB extends Template {
  public static final Identifier TEMPLATE_ID =
      new Identifier("SomePackage", "SomeModule", "TemplateB");

  public final String argument;

  public TemplateB(String argument) {
    this.argument = argument;
  }

  @Override
  public CreateCommand create() {
    throw new IllegalStateException("unreachable code");
  }

  public static TemplateB fromValue(Value value$) throws IllegalArgumentException {
    Record record$ = value$.asRecord().get();
    List<Record.Field> fields$ = record$.getFields();
    String argument = fields$.get(0).getValue().asText().get().getValue();
    return new TemplateB(argument);
  }
}
