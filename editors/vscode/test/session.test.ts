import { describe, expect, it } from "vitest";
import { FrameDecoder, encodeFrame } from "../src/session.js";

describe("session framing", () => {
  it("round-trips a frame, including multibyte content", () => {
    const decoder = new FrameDecoder();
    const body = JSON.stringify({ value: "λϝ → 42" });
    expect(decoder.push(encodeFrame(body))).toEqual([body]);
  });

  it("reassembles frames split across chunks and batches", () => {
    const decoder = new FrameDecoder();
    const first = JSON.stringify({ id: 1 });
    const second = JSON.stringify({ id: 2, value: "ok" });
    const stream = Buffer.concat([encodeFrame(first), encodeFrame(second)]);
    const cut = encodeFrame(first).length - 3;
    expect(decoder.push(stream.subarray(0, 5))).toEqual([]);
    expect(decoder.push(stream.subarray(5, cut))).toEqual([]);
    expect(decoder.push(stream.subarray(cut))).toEqual([first, second]);
  });

  it("resynchronizes past a garbage header", () => {
    const decoder = new FrameDecoder();
    const body = JSON.stringify({ ok: true });
    const noise = Buffer.from("Warning: something\r\n\r\n", "ascii");
    expect(decoder.push(Buffer.concat([noise, encodeFrame(body)]))).toEqual([body]);
  });
});
