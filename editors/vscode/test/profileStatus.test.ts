import { describe, expect, it } from "vitest";
import { parseProjectProfile } from "../src/projects.js";

describe("parseProjectProfile", () => {
  it("reads the declared profile", () => {
    expect(
      parseProjectProfile(
        "<Project><PropertyGroup><IronKernelProfile>safe</IronKernelProfile></PropertyGroup></Project>"
      )
    ).toBe("safe");
  });

  it("tolerates whitespace and returns undefined for junk or absence", () => {
    expect(
      parseProjectProfile("<IronKernelProfile>\n  minimal\n</IronKernelProfile>")
    ).toBe("minimal");
    expect(parseProjectProfile("<IronKernelProfile>root</IronKernelProfile>")).toBeUndefined();
    expect(parseProjectProfile("<Project />")).toBeUndefined();
  });
});
