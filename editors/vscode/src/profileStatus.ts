import { promises as fs } from "node:fs";
import * as vscode from "vscode";
import { findIkprojWalkingUp, isIkprojPath, parseProjectProfile } from "./projects.js";

export class ProfileStatus {
  private readonly item: vscode.StatusBarItem;

  constructor() {
    this.item = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    this.item.command = "ironkernel.selectProfile";
  }

  dispose(): void {
    this.item.dispose();
  }

  async update(): Promise<void> {
    const editor = vscode.window.activeTextEditor;
    const document = editor?.document;
    const relevant =
      document !== undefined &&
      (document.languageId === "ironkernel" || isIkprojPath(document.uri.fsPath));
    if (!document || !relevant) {
      this.item.hide();
      return;
    }

    const profile = vscode.workspace
      .getConfiguration("ironkernel", document.uri)
      .get<string>("profile", "unrestricted");

    let projectProfile: string | undefined;
    try {
      const ikproj = isIkprojPath(document.uri.fsPath)
        ? document.uri.fsPath
        : await findIkprojWalkingUp(document.uri.fsPath);
      if (ikproj) {
        projectProfile = parseProjectProfile(await fs.readFile(ikproj, "utf8"));
      }
    } catch {
      // No readable project; the setting alone is the story.
    }

    if (projectProfile && projectProfile !== profile) {
      this.item.text = `$(shield) IK: ${profile} (project: ${projectProfile})`;
      this.item.tooltip =
        `IronKernel capability profile: ${profile} (ironkernel.profile setting).\n` +
        `The project declares '${projectProfile}', but editor commands pass ` +
        `--profile ${profile}, which overrides it. Click to change.`;
    } else {
      this.item.text = `$(shield) IK: ${profile}`;
      this.item.tooltip =
        `IronKernel capability profile: ${profile}. Applies to run/compile ` +
        `commands, the playground, and the language server. Click to change.`;
    }
    this.item.show();
  }
}
