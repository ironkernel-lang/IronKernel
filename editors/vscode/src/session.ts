import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import type { RuntimeCommand } from "./cli.js";

export function encodeFrame(json: string): Buffer {
  const body = Buffer.from(json, "utf8");
  return Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, "ascii"), body]);
}

/** Incremental Content-Length frame decoder; push chunks, get JSON bodies. */
export class FrameDecoder {
  private buffer = Buffer.alloc(0);

  push(chunk: Buffer): string[] {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    const bodies: string[] = [];
    for (;;) {
      const headerEnd = this.buffer.indexOf("\r\n\r\n");
      if (headerEnd < 0) {
        break;
      }
      const headers = this.buffer.subarray(0, headerEnd).toString("ascii");
      const match = /content-length:\s*(\d+)/i.exec(headers);
      if (!match) {
        // Unframeable garbage; drop the broken header and resynchronize.
        this.buffer = this.buffer.subarray(headerEnd + 4);
        continue;
      }
      const length = Number.parseInt(match[1] ?? "0", 10);
      const frameEnd = headerEnd + 4 + length;
      if (this.buffer.length < frameEnd) {
        break;
      }
      bodies.push(this.buffer.subarray(headerEnd + 4, frameEnd).toString("utf8"));
      this.buffer = this.buffer.subarray(frameEnd);
    }
    return bodies;
  }
}

export interface SessionErrorLocation {
  file: string;
  range: { start: { line: number; column: number }; end: { line: number; column: number } };
}

export interface SessionEvalResult {
  output: string;
  value?: string;
  inert?: boolean;
  error?: { message: string; rendered: string; locations: SessionErrorLocation[] };
}

interface PendingRequest {
  resolve: (value: unknown) => void;
  reject: (reason: Error) => void;
  timer: NodeJS.Timeout;
}

/**
 * One `ik session` child process: persistent evaluation with structured
 * results. The client owns the timeout — a hung evaluation kills the process
 * and the next request starts a fresh session (losing its definitions, which
 * the caller should surface).
 */
export class SessionClient {
  private child: ChildProcessWithoutNullStreams | undefined;
  private decoder = new FrameDecoder();
  private readonly pending = new Map<number, PendingRequest>();
  private nextId = 1;

  constructor(
    private readonly runtime: RuntimeCommand,
    private readonly requestTimeoutMs: number
  ) {}

  get running(): boolean {
    return this.child !== undefined;
  }

  private start(): ChildProcessWithoutNullStreams {
    const child = spawn(this.runtime.command, [...this.runtime.prefixArgs, "session"], {
      cwd: this.runtime.cwd,
      shell: false,
      windowsHide: true
    });
    this.decoder = new FrameDecoder();
    child.stdout.on("data", (chunk: Buffer) => {
      for (const body of this.decoder.push(chunk)) {
        this.dispatch(body);
      }
    });
    child.on("close", () => {
      if (this.child === child) {
        this.child = undefined;
      }
      this.rejectAll(new Error("The IronKernel session ended."));
    });
    child.on("error", () => {
      if (this.child === child) {
        this.child = undefined;
      }
      this.rejectAll(new Error("The IronKernel session could not start."));
    });
    this.child = child;
    return child;
  }

  private dispatch(body: string): void {
    let parsed: { id?: number; result?: unknown; error?: { message?: string } };
    try {
      parsed = JSON.parse(body) as typeof parsed;
    } catch {
      return;
    }
    if (typeof parsed.id !== "number") {
      return;
    }
    const waiting = this.pending.get(parsed.id);
    if (!waiting) {
      return;
    }
    this.pending.delete(parsed.id);
    clearTimeout(waiting.timer);
    if (parsed.error) {
      waiting.reject(new Error(parsed.error.message ?? "session protocol error"));
    } else {
      waiting.resolve(parsed.result);
    }
  }

  private rejectAll(reason: Error): void {
    for (const [, waiting] of this.pending) {
      clearTimeout(waiting.timer);
      waiting.reject(reason);
    }
    this.pending.clear();
  }

  request<T>(method: string, params: unknown): Promise<T> {
    const child = this.child ?? this.start();
    const id = this.nextId;
    this.nextId += 1;
    return new Promise<T>((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        // A hung evaluation cannot be interrupted; killing the session is
        // the interrupt story, and the next request begins a fresh one.
        this.kill();
        reject(new Error(`The session did not answer within ${this.requestTimeoutMs} ms and was restarted.`));
      }, this.requestTimeoutMs);
      this.pending.set(id, {
        resolve: (value) => resolve(value as T),
        reject,
        timer
      });
      child.stdin.write(
        encodeFrame(JSON.stringify({ jsonrpc: "2.0", id, method, params }))
      );
    });
  }

  eval(code: string): Promise<SessionEvalResult> {
    return this.request<SessionEvalResult>("eval", { code });
  }

  kill(): void {
    const child = this.child;
    this.child = undefined;
    if (child) {
      child.kill();
    }
    this.rejectAll(new Error("The IronKernel session was restarted."));
  }

  dispose(): void {
    const child = this.child;
    this.child = undefined;
    if (child) {
      child.stdin.write(encodeFrame(JSON.stringify({ jsonrpc: "2.0", method: "exit" })));
      setTimeout(() => child.kill(), 500);
    }
    this.rejectAll(new Error("The IronKernel session was disposed."));
  }
}
