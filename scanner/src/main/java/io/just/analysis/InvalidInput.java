package io.just.analysis;

/** An invalid scan selection or supplied snapshot, identified at its input boundary. */
public final class InvalidInput extends IllegalArgumentException {
    public InvalidInput(String detail) { super(detail); }
}
