import { promises as fs } from "node:fs";
import * as path from "node:path";

/** True when `candidate` is an IronKernel project file. */
export function isIkprojPath(filePath: string): boolean {
  return path.extname(filePath).toLowerCase() === ".ikproj";
}

/**
 * Walk from a source file's directory toward the filesystem root and return the
 * unique `.ikproj` in the nearest ancestor that contains exactly one.
 */
export async function findIkprojWalkingUp(startFile: string): Promise<string | undefined> {
  let directory = path.dirname(path.resolve(startFile));
  const { root } = path.parse(directory);

  while (true) {
    let entries: string[];
    try {
      entries = await fs.readdir(directory);
    } catch {
      break;
    }

    const matches = entries
      .filter((entry) => entry.toLowerCase().endsWith(".ikproj"))
      .map((entry) => path.join(directory, entry))
      .sort((left, right) => left.localeCompare(right));

    if (matches.length === 1) {
      return matches[0];
    }
    if (matches.length > 1) {
      // Ambiguous at this level — let the caller present a picker.
      return undefined;
    }

    if (directory === root) {
      break;
    }
    const parent = path.dirname(directory);
    if (parent === directory) {
      break;
    }
    directory = parent;
  }

  return undefined;
}

/** Prefer projects whose directory contains `activePath`, then path order. */
export function rankIkProjects(activePath: string | undefined, projects: string[]): string[] {
  const resolved = projects.map((project) => path.resolve(project));
  if (!activePath) {
    return [...resolved].sort((left, right) => left.localeCompare(right));
  }

  const active = path.resolve(activePath);
  return [...resolved].sort((left, right) => {
    const leftContains = active === left || active.startsWith(path.dirname(left) + path.sep);
    const rightContains = active === right || active.startsWith(path.dirname(right) + path.sep);
    if (leftContains !== rightContains) {
      return leftContains ? -1 : 1;
    }
    const leftDepth = path.dirname(left).length;
    const rightDepth = path.dirname(right).length;
    if (leftContains && rightContains && leftDepth !== rightDepth) {
      // Prefer the more nested (closer) project.
      return rightDepth - leftDepth;
    }
    return left.localeCompare(right);
  });
}

/**
 * The project's own declared profile, if the .ikproj carries one. The
 * extension always passes --profile from the setting, which overrides this;
 * the status bar surfaces the mismatch instead of leaving it a surprise.
 */
export function parseProjectProfile(xml: string): string | undefined {
  const match =
    /<IronKernelProfile>\s*(minimal|safe|unrestricted)\s*<\/IronKernelProfile>/.exec(xml);
  return match?.[1];
}
