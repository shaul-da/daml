// Copyright (c) 2019 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.ledger.javaapi.data;

import com.digitalasset.ledger.api.v1.TransactionOuterClass;

import java.time.Instant;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class Transaction implements WorkflowEvent {

    private final String transactionId;

    private final String commandId;

    private final String workflowId;

    private final Instant effectiveAt;

    private final java.util.List<Event> events;

    private final String offset;

    public Transaction(String transactionId, String commandId, String workflowId, Instant effectiveAt, List<Event> events, String offset) {
        this.transactionId = transactionId;
        this.commandId = commandId;
        this.workflowId = workflowId;
        this.effectiveAt = effectiveAt;
        this.events = events;
        this.offset = offset;
    }

    public static Transaction fromProto(TransactionOuterClass.Transaction transaction) {
        String transactionId = transaction.getTransactionId();
        String commandId = transaction.getCommandId();
        Instant effectiveAt = Instant.ofEpochSecond(transaction.getEffectiveAt().getSeconds(), transaction.getEffectiveAt().getNanos());
        String workflowId = transaction.getWorkflowId();
        java.util.List<Event> events = transaction.getEventsList().stream().map(Event::fromProtoEvent).collect(Collectors.toList());
        String offset = transaction.getOffset();
        return new Transaction(transactionId, commandId, workflowId, effectiveAt, events, offset);
    }

    public TransactionOuterClass.Transaction toProto() {
        return TransactionOuterClass.Transaction.newBuilder()
                .setTransactionId(this.transactionId)
                .setCommandId(this.commandId)
                .setEffectiveAt(com.google.protobuf.Timestamp.newBuilder().setSeconds(this.effectiveAt.getEpochSecond()).setNanos(this.effectiveAt.getNano()).build())
                .addAllEvents(this.events.stream().map(Event::toProtoEvent).collect(Collectors.toList()))
                .setOffset(this.offset)
                .build();
    }

    public String getTransactionId() {
        return transactionId;
    }

    public String getCommandId() {
        return commandId;
    }

    public Instant getEffectiveAt() {
        return effectiveAt;
    }

    public List<Event> getEvents() {
        return events;
    }

    public String getOffset() {
        return offset;
    }

    public String getWorkflowId() {
        return workflowId;
    }

    @Override
    public String toString() {
        return "Transaction{" +
                "transactionId='" + transactionId + '\'' +
                ", commandId='" + commandId + '\'' +
                ", workflowId='" + workflowId + '\'' +
                ", effectiveAt=" + effectiveAt +
                ", events=" + events +
                ", offset='" + offset + '\'' +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Transaction that = (Transaction) o;
        return Objects.equals(transactionId, that.transactionId) &&
                Objects.equals(commandId, that.commandId) &&
                Objects.equals(workflowId, that.workflowId) &&
                Objects.equals(effectiveAt, that.effectiveAt) &&
                Objects.equals(events, that.events) &&
                Objects.equals(offset, that.offset);
    }

    @Override
    public int hashCode() {

        return Objects.hash(transactionId, commandId, workflowId, effectiveAt, events, offset);
    }
}
