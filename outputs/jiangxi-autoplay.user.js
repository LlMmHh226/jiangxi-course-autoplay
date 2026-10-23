// ==UserScript==
// @name         江西课程自动连播与十分钟刷新
// @namespace    codex.local
// @version      4.7.0
// @description  自动连播、后台播放、十分钟强制刷新与倍速记忆；优先平台原生倍速，检测回退后停止反复调速。
// @match        https://jiangxi.zhipeizaixian.com/*
// @run-at       document-start
// @grant        GM_openInTab
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_getTab
// @grant        GM_saveTab
// @grant        GM_getTabs
// @grant        window.close
// @noframes
// ==/UserScript==

(function () {
  "use strict";
  if (window.top !== window.self) return;

  const INSTANCE = "__codexJiangxiAutoplayV2";
  window[INSTANCE]?.destroy();
  const PANEL_ID = "codex-course-autonext-panel-v2";
  const WAIT_MS = 30_000;
  const SETTLE_MS = 1_500;
  const REFRESH_MS = 600_000;
  const RUNTIME_FIELD = "codexJxRuntimeV4";
  const LOG_PREFIX = "codex-jx-log-v4:";
  const BACKUP_PREFIX = "codex-jx-runtime-backup-v42:";
  const DOCUMENT_ID = crypto.randomUUID();
  const BRIDGE_PARAM = "__codex_jx_handoff";
  const TRANSFER_PREFIX = "codex-jx-transfer-v4:";
  const ATTEMPTS_KEY = "codex-jx-attempts-v4";
  const TAB_FIELD = "codexJxAutoplayTabV3";
  const BRIDGE_TIMEOUT_MS = 90_000;
  const RELEASE_DELAY_MS = 2_500;
  const SPEEDS = [1, 1.25, 1.5, 2];
  const SPEED_PREF_PREFIX = "codex-jx-speed-v45:";
  const SPEED_LIMIT_PREFIX = "codex-jx-speed-limit-v46:";
  const bridgeToken = location.pathname === "/" ? new URL(location.href).searchParams.get(BRIDGE_PARAM) : null;
  // 平台会显示“下一单元”和“3秒后播放下一节”，不是固定的“下一节”。
  const NEXT_TEXT = /^(?:(?:\d+(?:\.\d+)?\s*(?:秒|s)\s*后\s*)?(?:自动\s*)?播放\s*)?下一\s*(?:节|课|讲|单元)(?:\s*[:：\-—>›].*)?$/i;
  const VERIFY_TEXT = /验证码|人机验证|安全验证|身份验证|人脸|请完成验证|滑动验证|拖动滑块|captcha|verify you are human/i;
  const DIALOG_SELECTOR = 'dialog[open], [role="dialog"], .gateway-modal-content, .ant-modal-content, [class*="content_modal___"]';
  const CONTROL_SELECTOR = 'button, a, [role="button"], [tabindex]:not([tabindex="-1"]), [class*="btn" i]';

  let paused = false;
  let pauseReason = "";
  let phase = "idle"; // idle | waiting | handoff | done
  let deadline = 0;
  let endedRecord = null;
  let activeKey = "";
  let wantPlay = true;
  let playPending = false;
  let playGeneration = 0;
  let playDeadline = 0;
  let nextPlayAt = 0;
  let needsGesture = false;
  let host, statusElement, toggleButton, playButton, reopenButton, closeButton;
  let countdownElement, refreshButton, refreshToggle, historyElement;
  let outgoing = null;
  let loadingSince = 0;
  let timer = null;
  let disposed = false;
  let runtime = null;
  let runtimeReady = false;
  let runtimeError = "";
  let runtimeInit = null;
  let metadataQueue = Promise.resolve();
  let refreshJob = null;
  let restoreIntent = null;
  let events = [];
  let lastPlayingKey = "";
  let backgroundToggle;
  let backgroundJob = null;
  let backgroundWanted = false;
  let backgroundAttempts = [];
  let backgroundProof = null;
  let mediaSessionInstalled = false;
  let metadataWarning = false;
  let speedSelect, speedInfo;
  let speedState = null;
  let changingSpeed = false;

  function onCoursePage() {
    return location.pathname.replace(/\/$/, "") === "/study/video";
  }

  function visible(element) {
    if (!(element instanceof Element) || !element.isConnected) return false;
    const style = getComputedStyle(element);
    const rect = element.getBoundingClientRect();
    return style.display !== "none" && style.visibility !== "hidden" &&
      Number(style.opacity) !== 0 && rect.width > 0 && rect.height > 0 &&
      !element.closest('[hidden], [aria-hidden="true"]');
  }

  function enabled(element) {
    return !element.matches(':disabled, [aria-disabled="true"], [aria-busy="true"]') &&
      !element.closest('[aria-disabled="true"], .disabled, .is-disabled') &&
      getComputedStyle(element).pointerEvents !== "none";
  }

  function text(value) {
    return String(value || "").replace(/\s+/g, " ").trim();
  }

  function routeKey(href = location.href) {
    const url = new URL(href, location.href);
    return [url.pathname, ...["course_id", "unit_id", "class_id"].map(k => url.searchParams.get(k) || "")].join("|");
  }

  function source(video) {
    return video ? video.currentSrc || video.getAttribute("src") || "" : "";
  }

  function mediaKey(video) {
    return `${routeKey()}|${source(video)}`;
  }

  function courseVideo() {
    // 排除人脸验证窗口内的摄像头 video，优先识别平台课程播放器。
    const videos = [...document.querySelectorAll("video")].filter(video =>
      !video.srcObject && !video.closest(DIALOG_SELECTOR));
    const players = videos.filter(video => video.closest('.prism-player, [class*="video_wrap___"]') &&
      (visible(video) || (video.isConnected && !video.closest('[hidden], [aria-hidden="true"]') &&
        source(video) && video.readyState >= 1 && Number.isFinite(video.duration) && video.duration > 0)));
    // 部分播放器用其它图层显示画面，或在后台把原始 video 尺寸设为零。
    // 已有真实媒体元数据的课程 video 仍需跟踪，不能把零尺寸当成未加载。
    return (players.length ? players : videos.filter(visible)).sort((a, b) => {
      const ar = a.getBoundingClientRect(), br = b.getBoundingClientRect();
      return br.width * br.height - ar.width * ar.height;
    })[0] || null;
  }

  function blockingPrompt() {
    for (const element of document.querySelectorAll(DIALOG_SELECTOR)) {
      if (visible(element)) {
        return VERIFY_TEXT.test(element.innerText || element.textContent || "")
          ? "请手动完成页面验证，再点“继续连播”。"
          : "页面有弹窗，请手动处理后点“继续连播”。";
      }
    }
    for (const frame of document.querySelectorAll('iframe[src*="captcha" i], iframe[src*="verify" i]')) {
      if (visible(frame)) return "请手动完成页面验证，再点“继续连播”。";
    }
    return "";
  }

  function status(message, warning = false) {
    if (!statusElement) return;
    if (statusElement.textContent !== message) statusElement.textContent = message;
    statusElement.dataset.warning = String(warning);
    toggleButton.textContent = paused ? "继续连播" : "暂停连播";
    playButton.hidden = paused || !needsGesture;
    toggleButton.hidden = Boolean(bridgeToken);
    reopenButton.hidden = Boolean(bridgeToken) || Boolean(outgoing);
    closeButton.hidden = !outgoing?.closing;
    refreshButton.hidden = Boolean(bridgeToken) || Boolean(outgoing);
    refreshButton.disabled = !runtimeReady || Boolean(refreshJob);
    refreshToggle.hidden = Boolean(bridgeToken) || Boolean(outgoing);
    refreshToggle.disabled = !runtimeReady || Boolean(refreshJob);
    renderClock();
  }

  function panel() {
    if (host?.isConnected) return true;
    if (!document.documentElement) return false;
    document.getElementById(PANEL_ID)?.remove();
    host = document.createElement("div");
    host.id = PANEL_ID;
    host.dataset.version = "4.7.0";
    host.dataset.documentId = DOCUMENT_ID;
    host.style.cssText = "all:initial!important;position:fixed!important;right:16px!important;bottom:16px!important;z-index:2147483647!important";
    const shadow = host.attachShadow({ mode: "open" });
    shadow.innerHTML = `
      <style>
        :host{all:initial}.card{box-sizing:border-box;width:340px;padding:13px 15px;background:#20242b;color:#f7f8fa;border:1px solid #454b55;border-radius:10px;box-shadow:0 5px 24px #0005;font:13px/1.5 system-ui,sans-serif}
        .top{display:flex;align-items:center;justify-content:space-between;gap:10px}.title{font-weight:650}.status{margin-top:8px;overflow-wrap:anywhere;color:#d2d7df}.status[data-warning=true]{color:#ffd27a}.hint{margin-top:8px;font-size:11px;color:#adb6c3}
        button{border:0;border-radius:6px;padding:5px 10px;color:white;background:#465363;font:inherit;cursor:pointer}button:hover{background:#5a6a7d}button:focus-visible,select:focus-visible{outline:2px solid #94c5ff;outline-offset:2px}button:disabled{opacity:.5;cursor:default}.play{margin-top:9px;background:#285fa3}.actions{display:flex;flex-wrap:wrap;gap:6px;margin-top:9px}.clock{margin-top:8px;color:#9ecbff}.speed-row{display:flex;align-items:center;gap:8px;margin-top:8px}.speed-row select{font:inherit;background:#34404e;color:#fff;border:1px solid #687584;border-radius:5px;padding:3px 5px}.speed-info{font-size:11px;color:#adb6c3}.speed-info[data-warning=true]{color:#ffd27a}details{margin-top:8px;color:#b8c3d3;font-size:11px}summary{cursor:pointer}.history{padding-left:18px;max-height:140px;overflow:auto;margin:6px 0}.history li{margin:3px 0}[hidden]{display:none!important}
      </style>
      <section class="card" aria-label="课程自动连播助手">
        <div class="top"><span class="title">连播、刷新与倍速 · 4.7</span><button class="toggle" type="button">暂停连播</button></div>
        <div class="status" role="status" aria-live="polite"></div>
        <div class="clock"></div>
        <div class="speed-row"><label for="course-speed">播放倍速</label><select id="course-speed" aria-label="播放倍速"><option value="0">跟随播放器</option><option value="1">1 倍</option><option value="1.25">1.25 倍</option><option value="1.5">1.5 倍</option><option value="2">2 倍</option></select></div>
        <div class="speed-info" role="status" aria-live="polite"></div>
        <button class="play" type="button" hidden>播放本节</button>
        <div class="actions"><button class="refresh" type="button">立即刷新</button><button class="refresh-toggle" type="button">关闭定时刷新</button><button class="background-toggle" type="button">关闭后台播放</button><button class="reopen" type="button">重新打开本节</button><button class="close" type="button" hidden>关闭本页并继续</button></div>
        <div class="hint">每十分钟强制刷新并自动运行；暂停连播不影响刷新。验证需手动完成。</div>
        <details><summary>运行记录</summary><ol class="history"></ol></details>
      </section>`;
    statusElement = shadow.querySelector(".status");
    toggleButton = shadow.querySelector(".toggle");
    playButton = shadow.querySelector(".play");
    reopenButton = shadow.querySelector(".reopen");
    closeButton = shadow.querySelector(".close");
    countdownElement = shadow.querySelector(".clock");
    refreshButton = shadow.querySelector(".refresh");
    refreshToggle = shadow.querySelector(".refresh-toggle");
    backgroundToggle = shadow.querySelector(".background-toggle");
    historyElement = shadow.querySelector(".history");
    speedSelect = shadow.querySelector("select");
    speedInfo = shadow.querySelector(".speed-info");
    speedSelect.addEventListener("change", () => chooseSpeed(Number(speedSelect.value)));
    toggleButton.addEventListener("click", toggle);
    reopenButton.addEventListener("click", () => { void beginHandoff(location.href, true, "manual-reopen"); });
    refreshButton.addEventListener("click", () => { void requestRefresh(true); });
    refreshToggle.addEventListener("click", () => {
      if (!runtimeReady || refreshJob || outgoing) return;
      runtime = { ...runtime, enabled: !runtime.enabled, nextAt: Date.now() + REFRESH_MS };
      saveRuntimeInBackground();
      appendEvent("refresh-option", runtime.enabled ? "已开启十分钟定时刷新" : "已关闭定时刷新");
      renderClock();
    });
    backgroundToggle.addEventListener("click", () => {
      if (!runtimeReady || outgoing || refreshJob) return;
      runtime = { ...runtime, backgroundEnabled: !runtime.backgroundEnabled };
      if (!runtime.backgroundEnabled) cancelBackground();
      saveRuntimeInBackground();
      appendEvent("background-option", runtime.backgroundEnabled ? "已开启后台播放" : "已关闭后台播放");
      renderClock();
    });
    closeButton.addEventListener("click", closeCurrent);
    playButton.addEventListener("click", () => {
      const prompt = blockingPrompt();
      if (prompt) return pause(prompt, "prompt");
      needsGesture = false;
      wantPlay = true;
      nextPlayAt = 0;
      play(courseVideo(), true);
    });
    document.documentElement.appendChild(host);
    renderHistory();
    status("已开启，正在查找课程视频");
    return true;
  }

  function pause(message, reason = "user") {
    cancelOutgoing();
    cancelBackground();
    paused = true;
    pauseReason = reason;
    playGeneration++; // 忽略已经失效的 play() Promise 回调。
    playPending = false;
    if (runtimeReady) {
      runtime = { ...runtime, paused: reason === "user", pauseReason: reason === "user" ? "user" : "" };
      saveRuntimeInBackground();
      appendEvent("paused", message);
    }
    status(message, true);
  }

  function toggle() {
    if (!runtimeReady) return status(runtimeError || "正在读取刷新计时，请稍候。", true);
    if (!paused) return pause("已暂停自动连播，视频播放由你控制。");
    const prompt = blockingPrompt();
    if (prompt) return status(prompt, true);
    paused = false;
    runtime = { ...runtime, paused: false, pauseReason: "" };
    saveRuntimeInBackground();
    appendEvent("resumed", "已继续连播，十分钟强制刷新仍按原计划计时");
    const video = courseVideo();
    // 继续时重新给足等待时间。
    deadline = Date.now() + WAIT_MS;
    if (video?.ended && endedRecord?.route === routeKey()) {
      startWaiting(video);
    }
    pauseReason = "";
    if (phase === "idle" && video && !video.ended) {
      wantPlay = true;
      needsGesture = false;
      nextPlayAt = 0;
      play(video, true);
    } else {
      status("已继续，正在重新检查当前课程");
      tick();
    }
  }

  function nextControls() {
    const matching = [...document.querySelectorAll(CONTROL_SELECTOR)].filter(element =>
      visible(element) && [element.innerText || element.textContent,
        element.getAttribute("aria-label"), element.getAttribute("title")]
        .some(label => NEXT_TEXT.test(text(label))));
    const controls = matching.filter(element => !matching.some(other => other !== element && element.contains(other)));
    // 使用已核对的平台结束浮层；只凭 class 不点击，仍要求文字匹配。
    const native = controls.filter(element => element.closest('[class*="modal_mark___"]') &&
      element.matches('[class*="next_button___"]'));
    return native.length ? native : controls;
  }

  function safeUnitUrl(href, reference = location.href) {
    try {
      const url = new URL(href, location.href), current = new URL(reference, location.href);
      if (url.origin !== location.origin || current.origin !== location.origin || url.pathname !== "/study/video" ||
        !/^\d+$/.test(url.searchParams.get("course_id") || "") ||
        !/^\d+$/.test(url.searchParams.get("unit_id") || "") ||
        ["course_id", "class_id"].some(key => url.searchParams.get(key) !== current.searchParams.get(key))) return null;
      return url.href;
    } catch { return null; }
  }

  function compactTitle(value) {
    return text(value).replace(/[（(]\s*(?:\d+:)?\d{1,2}:\d{2}\s*[）)]\s*$/, "").replace(/\s/g, "");
  }

  function nextUnitUrl(control) {
    const endPanel = control.closest('[class*="modal_mark___"]');
    const intro = endPanel?.querySelector("p");
    if (!intro) return null;
    // 浮层里 span 是“视频”等类型标签，只比较直接文本中的单元标题。
    const title = compactTitle([...intro.childNodes].filter(node => node.nodeType === Node.TEXT_NODE)
      .map(node => node.textContent).join("").replace(/^\s*下一单元\s*[:：]/, ""));
    if (!title) return null;
    const urls = new Set();
    for (const link of document.querySelectorAll('a[class*="units_wrap_box___"][href]')) {
      if (compactTitle(link.innerText || link.textContent) !== title) continue;
      const url = safeUnitUrl(link.getAttribute("href"));
      if (url) urls.add(url);
    }
    return urls.size === 1 ? [...urls][0] : null;
  }

  function hasTabApis() {
    return typeof GM_openInTab === "function" && typeof GM_getValue === "function" &&
      typeof GM_setValue === "function" && typeof GM_deleteValue === "function" &&
      typeof GM_getTab === "function" && typeof GM_saveTab === "function" && typeof GM_getTabs === "function";
  }

  function mutateTabMetadata(mutate) {
    const operation = metadataQueue.catch(() => {}).then(() => new Promise((resolve, reject) => {
      let settled = false;
      const timeout = window.setTimeout(() => finish(new Error("tab metadata timeout")), 5_000);
      function finish(error, result) {
        if (settled) return;
        settled = true;
        window.clearTimeout(timeout);
        error ? reject(error) : resolve(result);
      }
      try {
        GM_getTab(saved => {
          try {
            const data = saved || {};
            if (!data[TAB_FIELD]) data[TAB_FIELD] = crypto.randomUUID();
            const result = mutate(data);
            GM_saveTab(data, () => finish(null, result));
          } catch (error) { finish(error); }
        });
      } catch (error) { finish(error); }
    }));
    metadataQueue = operation;
    return operation;
  }

  function selfTabId() {
    return mutateTabMetadata(data => data[TAB_FIELD]);
  }

  function clockOwner(href = location.href) {
    const url = new URL(href, location.href);
    return [url.searchParams.get("course_id") || "", url.searchParams.get("class_id") || ""].join("|");
  }

  function normalizeRuntime(value, href = location.href) {
    const now = Date.now(), owner = clockOwner(href);
    const valid = value && value.schema === 4 && value.owner === owner && typeof value.chainId === "string";
    const stored = valid ? value : {};
    return {
      schema: 4, owner, chainId: stored.chainId || crypto.randomUUID(),
      refreshMode: "forced", savedAt: Number.isFinite(stored.savedAt) ? stored.savedAt : 0,
      enabled: stored.refreshMode === "forced" ? stored.enabled !== false : true,
      paused: stored.refreshMode === "forced" && stored.paused === true && stored.pauseReason === "user",
      pauseReason: stored.refreshMode === "forced" && stored.pauseReason === "user" ? "user" : "",
      backgroundEnabled: stored.backgroundEnabled !== false,
      nextAt: Number.isFinite(stored.nextAt) && stored.nextAt > 0 && stored.nextAt <= now + REFRESH_MS + 60_000
        ? stored.nextAt : now + REFRESH_MS,
      refreshCount: Number.isSafeInteger(stored.refreshCount) && stored.refreshCount >= 0 ? stored.refreshCount : 0,
      timedRefreshCount: Number.isSafeInteger(stored.timedRefreshCount) && stored.timedRefreshCount >= 0 ? stored.timedRefreshCount : 0,
      lastRefreshAt: Number.isFinite(stored.lastRefreshAt) ? stored.lastRefreshAt : null,
      resumePlayback: stored.resumePlayback !== false,
      playbackSpeed: [0, ...SPEEDS].includes(stored.playbackSpeed) ? stored.playbackSpeed : readSpeedPreference(owner),
      speedBlockedRoute: typeof stored.speedBlockedRoute === "string" ? stored.speedBlockedRoute : "",
      speedNativeOnly: stored.speedNativeOnly === true ||
        (typeof stored.speedBlockedRoute === "string" && Boolean(stored.speedBlockedRoute)) || readSpeedLimit(owner),
      pendingRefresh: stored.pendingRefresh && typeof stored.pendingRefresh.id === "string" ? stored.pendingRefresh : null
    };
  }

  function persistRuntime(snapshot = runtime) {
    if (snapshot) snapshot.savedAt = Math.max(Date.now(), (snapshot.savedAt || 0) + 1);
    const saved = snapshot ? structuredClone(snapshot) : null;
    // 标签页接口短暂异常也保留本标签页的刷新截止时间，不能因此停掉刷新。
    try { if (saved) sessionStorage.setItem(BACKUP_PREFIX + saved.owner, JSON.stringify(saved)); } catch {}
    return mutateTabMetadata(data => {
      if (saved) data[RUNTIME_FIELD] = saved;
      return saved;
    });
  }

  function saveRuntimeInBackground() {
    if (!runtimeReady || !runtime) return;
    void persistRuntime().catch(() => {
      if (disposed) return;
      if (!metadataWarning) appendEvent("metadata-warning", "标签页状态保存暂时失败，强制刷新计时继续运行");
      metadataWarning = true;
    });
  }

  function renderHistory() {
    if (!historyElement) return;
    historyElement.replaceChildren(...events.slice(-10).map(event => {
      const li = document.createElement("li");
      li.textContent = `${new Date(event.at).toLocaleTimeString()} ${event.label}`;
      return li;
    }));
  }

  function appendEvent(kind, label, href = location.href) {
    if (!runtime) return;
    const event = { at: Date.now(), kind, label, documentId: DOCUMENT_ID,
      unit: new URL(href, location.href).searchParams.get("unit_id") || "", chainId: runtime.chainId };
    try {
      const key = LOG_PREFIX + runtime.chainId;
      const stored = GM_getValue(key, []);
      events = [...(Array.isArray(stored) ? stored : []), event].slice(-80);
      GM_setValue(key, events);
    } catch { events = [...events, event].slice(-80); }
    renderHistory();
    console.info("[课程助手]", JSON.stringify(event));
  }

  function renderClock() {
    if (!countdownElement) return;
    countdownElement.hidden = Boolean(bridgeToken);
    if (bridgeToken) return;
    refreshToggle.textContent = runtime?.enabled === false ? "开启定时刷新" : "关闭定时刷新";
    backgroundToggle.hidden = Boolean(bridgeToken) || Boolean(outgoing);
    backgroundToggle.disabled = !runtimeReady || Boolean(refreshJob);
    backgroundToggle.textContent = runtime?.backgroundEnabled === false ? "开启后台播放" : "关闭后台播放";
    renderSpeed();
    if (!runtimeReady) { countdownElement.textContent = "正在读取十分钟刷新计时"; return; }
    if (!runtime.enabled) { countdownElement.textContent = "十分钟定时刷新已关闭"; return; }
    const seconds = Math.max(0, Math.ceil((runtime.nextAt - Date.now()) / 1_000));
    const countdown = `${String(Math.floor(seconds / 60)).padStart(2, "0")}:${String(seconds % 60).padStart(2, "0")}`;
    countdownElement.textContent = `下次强制刷新 ${countdown} · 已定时刷新 ${runtime.timedRefreshCount} 次`;
    countdownElement.dataset.nextAt = String(runtime.nextAt);
    countdownElement.dataset.completed = String(runtime.timedRefreshCount);
  }

  async function initializeRuntime() {
    let completed = null;
    let backup;
    try { backup = JSON.parse(sessionStorage.getItem(BACKUP_PREFIX + clockOwner()) || "null"); } catch {}
    const prepare = data => {
      const stored = data[RUNTIME_FIELD];
      const candidate = backup?.schema === 4 && backup.owner === clockOwner() &&
        backup.savedAt > (stored?.savedAt || 0) ? backup : stored;
      const clock = normalizeRuntime(candidate);
      if (clock.pendingRefresh && clock.pendingRefresh.documentId !== DOCUMENT_ID) {
        if (clock.pendingRefresh.route === routeKey()) {
          completed = clock.pendingRefresh.kind;
          clock.refreshCount++;
          if (completed === "periodic") clock.timedRefreshCount++;
          clock.lastRefreshAt = Date.now();
        }
        // 旧文档可能在慢速加载时已安排重试；新文档既已加载，就恢复正常十分钟周期。
        // 不能把仅属于旧文档的五秒重试截止时间带到新页面，导致紧接着再次刷新。
        if (Number.isFinite(clock.pendingRefresh.at) && clock.pendingRefresh.at <= Date.now()) {
          clock.nextAt = Math.max(clock.nextAt, clock.pendingRefresh.at + REFRESH_MS);
        }
        clock.pendingRefresh = null;
      }
      data[RUNTIME_FIELD] = clock;
      return clock;
    };
    let loaded;
    try { loaded = await mutateTabMetadata(prepare); }
    catch { completed = null; loaded = prepare({}); metadataWarning = true; }
    if (disposed) return;
    runtime = loaded;
    runtimeReady = true;
    paused = runtime.paused;
    pauseReason = runtime.pauseReason;
    restoreIntent = !paused && runtime.resumePlayback;
    try {
      const stored = GM_getValue(LOG_PREFIX + runtime.chainId, []);
      events = Array.isArray(stored) ? stored.slice(-80) : [];
    } catch { events = []; }
    appendEvent(completed ? "refresh-complete" : "page-ready", completed === "periodic"
      ? "十分钟刷新已完成，等待播放器继续" : completed ? "手动刷新已完成" : "课程助手已就绪，恢复刷新计时");
    status(paused ? "连播已手动暂停，十分钟强制刷新继续运行" : "已开启连播和十分钟强制刷新，等待播放器");
    tick();
  }

  function cancelRefresh() {
    if (!refreshJob) return;
    refreshJob.cancelled = true;
    refreshJob = null;
  }

  async function requestRefresh(manual = false) {
    if (!runtimeReady || refreshJob || disposed || !onCoursePage()) return;
    if (!manual && !runtime.enabled) return;
    // 到期刷新优先：取消尚未完成的接续，避免旧页刷新与新页并发播放。
    cancelOutgoing();
    const video = courseVideo();
    cancelBackground();
    const job = { id: crypto.randomUUID(), route: routeKey(), cancelled: false, committed: false,
      previousNextAt: runtime.nextAt, at: Date.now() };
    refreshJob = job;
    const resumePlayback = Boolean(video && !video.paused) || wantPlay ||
      Boolean(runtime.backgroundEnabled && backgroundWanted && runtime.resumePlayback);
    runtime = { ...runtime, nextAt: Date.now() + REFRESH_MS, resumePlayback,
      paused: pauseReason === "user", pauseReason: pauseReason === "user" ? "user" : "",
      pendingRefresh: { id: job.id, documentId: DOCUMENT_ID, route: job.route, kind: manual ? "manual" : "periodic", at: job.at } };
    playGeneration++;
    playPending = false;
    status(manual ? "正在刷新当前课程页面，刷新后自动运行" : "十分钟已到，强制刷新；新页面自动运行");
    try {
      try { await persistRuntime(); }
      catch { appendEvent("metadata-warning", "状态保存暂时失败，仍执行到期强制刷新"); }
      if (disposed || job.cancelled || refreshJob !== job) return;
      if (routeKey() !== job.route) {
        runtime.pendingRefresh.route = routeKey();
        try { await persistRuntime(); } catch {}
        if (disposed || job.cancelled || refreshJob !== job) return;
      }
      job.committed = true;
      appendEvent("refresh-request", manual ? "手动刷新当前页面" : "十分钟到期，强制刷新当前页面");
      location.reload();
    } catch {
      if (refreshJob === job) {
        retryRefresh();
      }
    }
  }

  function retryRefresh() {
    if (!refreshJob) return;
    refreshJob.cancelled = true;
    refreshJob = null;
    // 保留尚未确认的刷新请求。即使旧文档超时，新文档随后到达仍应确认这次刷新。
    runtime = { ...runtime, nextAt: Date.now() + 5_000 };
    saveRuntimeInBackground();
    appendEvent("refresh-retry", "刷新未完成，五秒后重试；脚本继续运行");
    status("刷新未完成，五秒后重试；脚本继续运行", true);
  }

  function readSpeedPreference(owner = clockOwner()) {
    try {
      const value = GM_getValue(SPEED_PREF_PREFIX + owner, 0);
      return [0, ...SPEEDS].includes(value) ? value : 0;
    } catch { return 0; }
  }

  function readSpeedLimit(owner = clockOwner()) {
    try { return GM_getValue(SPEED_LIMIT_PREFIX + owner, false) === true; } catch { return false; }
  }

  function renderSpeed() {
    if (!speedSelect || !speedInfo) return;
    speedSelect.closest(".speed-row").hidden = Boolean(bridgeToken);
    speedInfo.hidden = Boolean(bridgeToken);
    speedSelect.disabled = !runtimeReady || Boolean(outgoing) || Boolean(refreshJob);
    if (!runtimeReady) { speedInfo.textContent = "正在读取倍速设置"; return; }
    speedSelect.value = String(runtime.playbackSpeed);
    const video = courseVideo(), actual = video?.playbackRate;
    const blocked = runtime.speedBlockedRoute === routeKey() && runtime.playbackSpeed > 1;
    const waitingForNative = runtime.speedNativeOnly && runtime.playbackSpeed > 1 && video &&
      !nativeSpeedOption(video, runtime.playbackSpeed) && !speedState?.applied;
    speedInfo.dataset.warning = String(blocked || waitingForNative);
    speedInfo.textContent = blocked
      ? `本节检测到回退或倍速重置，已停止反复调速 · 当前 ${Number.isFinite(actual) ? actual : 1} 倍`
      : waitingForNative ? "本课程已检测到倍速限制；本节无原生选项，保持正常速度。可手动重新选择试用。"
      : !video ? "等待播放器；切课和刷新后会记住所选倍速。"
        : `当前 ${Number.isFinite(actual) ? actual : 1} 倍${runtime.playbackSpeed ? " · 已记住所选倍速" : " · 跟随播放器"}`;
  }

  function chooseSpeed(rate, apply = true) {
    if (!runtimeReady || ![0, ...SPEEDS].includes(rate)) return;
    runtime = { ...runtime, playbackSpeed: rate, speedBlockedRoute: "" };
    speedState = null;
    try { GM_setValue(SPEED_PREF_PREFIX + runtime.owner, rate); } catch {}
    saveRuntimeInBackground();
    appendEvent("speed-choice", rate ? `已选择 ${rate} 倍，刷新和切课后保持` : "倍速改为跟随播放器");
    if (apply) pollSpeed(courseVideo(), true);
    renderSpeed();
  }

  function nativeSpeedOption(video, rate) {
    const player = video?.closest('.prism-player, [class*="video_wrap___"]');
    const options = [...player?.querySelectorAll('.rate-components .rate-list [data-rate]') || []]
      .filter(option => Number(option.dataset.rate) === rate && !option.matches('[aria-disabled="true"], .disabled'));
    return options.length === 1 ? options[0] : null;
  }

  function writeSpeed(video, rate) {
    changingSpeed = true;
    try {
      // 原生组件调用播放器自己的 setSpeed；没有组件时才用 HTML 视频的实际播放倍速。
      const option = nativeSpeedOption(video, rate);
      if (option) option.click();
      else video.playbackRate = rate;
      if ("preservesPitch" in video) video.preservesPitch = true;
      return Boolean(option);
    } finally { changingSpeed = false; }
  }

  function protectSpeed(video, reason) {
    if (speedState?.blocked) return;
    if (speedState) speedState.blocked = true;
    const needsNative = !nativeSpeedOption(video, runtime.playbackSpeed);
    runtime = { ...runtime, speedBlockedRoute: routeKey(), speedNativeOnly: runtime.speedNativeOnly || needsNative };
    if (needsNative) { try { GM_setValue(SPEED_LIMIT_PREFIX + runtime.owner, true); } catch {} }
    try { writeSpeed(video, 1); } catch {}
    saveRuntimeInBackground();
    appendEvent("speed-protected", `${reason}，${Math.abs(video.playbackRate - 1) <= 0.02 ? "本节恢复正常速度，" : ""}停止反复调速`);
    renderSpeed();
  }

  function pollSpeed(video, immediate = false) {
    if (!runtimeReady || disposed || bridgeToken || outgoing || refreshJob || changingSpeed ||
      !onCoursePage() || !video || video.ended || blockingPrompt()) return;
    const key = mediaKey(video), rate = runtime.playbackSpeed;
    if (!speedState || speedState.video !== video || speedState.key !== key || speedState.rate !== rate) {
      speedState = { video, key, rate, readyAt: Date.now() + SETTLE_MS, applied: false,
        blocked: false, graceUntil: 0, lastPosition: video.currentTime, ignoreRollbackUntil: 0 };
    }
    const state = speedState;
    if (!rate || (rate > 1 && runtime.speedBlockedRoute === routeKey()) || state.blocked ||
      video.readyState < 2 || (!immediate && Date.now() < state.readyAt)) return;
    if (state.applied) {
      if (Date.now() >= state.graceUntil && Math.abs(video.playbackRate - rate) > 0.02) {
        protectSpeed(video, "倍速被播放器或其它扩展重置");
      }
      return;
    }
    // 已经实测受限的课程，不在每个新单元重复先加速再回退。
    // 用户在面板里重新选择速度时，允许一次明确的手动试用。
    if (rate > 1 && runtime.speedNativeOnly && !nativeSpeedOption(video, rate) && !immediate) {
      renderSpeed();
      return;
    }
    state.applied = true;
    state.lastPosition = video.currentTime;
    state.graceUntil = Date.now() + 2_000;
    try {
      const native = Math.abs(video.playbackRate - rate) <= 0.02 ? false : writeSpeed(video, rate);
      appendEvent("speed-applied", `已应用 ${rate} 倍${native ? "（平台倍速）" : ""}`);
    } catch { protectSpeed(video, "播放器未接受所选倍速"); }
    renderSpeed();
  }

  function onSpeedEvent(event) {
    if (!runtimeReady || disposed || outgoing || refreshJob || changingSpeed || !onCoursePage()) return;
    const video = event.target;
    if (!(video instanceof HTMLVideoElement) || video !== courseVideo()) return;
    pollSpeed(video);
    const state = speedState;
    if (event.type === "timeupdate" && state?.video === video && state.applied && state.rate > 1 && !state.blocked) {
      if (Date.now() >= state.graceUntil && Date.now() >= state.ignoreRollbackUntil &&
        video.currentTime < state.lastPosition - 1.5 && !blockingPrompt()) {
        // 只降低播放速度；绝不把时间跳回去，也不把平台退回的进度强行快进。
        protectSpeed(video, "检测到视频进度回退");
      }
      state.lastPosition = video.currentTime;
    }
    if (event.type === "ratechange") renderSpeed();
  }

  function onPlayerSpeedInput(event) {
    const target = event.target;
    if (!(target instanceof Element)) return;
    if (event.type === "click" && !changingSpeed) {
      const option = target.closest('.rate-components .rate-list [data-rate]');
      const video = courseVideo();
      if (option && video?.closest('.prism-player, [class*="video_wrap___"]')?.contains(option)) {
        const rate = Number(option.dataset.rate);
        if (SPEEDS.includes(rate)) chooseSpeed(rate, false);
      }
    }
    if (event.isTrusted && speedState && (event.type === "pointerdown" || event.type === "keydown") &&
      target.closest('.prism-player, [class*="video_wrap___"]')) {
      // 用户主动回看不作为平台回退处理。
      speedState.ignoreRollbackUntil = Date.now() + 5_000;
    }
  }

  function cancelOutgoing() {
    const transfer = outgoing;
    outgoing = null;
    if (!transfer) return;
    if (transfer.key) { try { GM_deleteValue(transfer.key); } catch {} }
    // 旧页还在时取消交接，下一节尚未加载；这次准备不应消耗重试次数。
    try {
      const attempts = GM_getValue(ATTEMPTS_KEY, {});
      if (attempts?.[transfer.attemptRoute] === transfer.created) {
        delete attempts[transfer.attemptRoute];
        GM_setValue(ATTEMPTS_KEY, attempts);
      }
    } catch {}
    try { transfer.tab?.close(); } catch {}
    if (phase === "handoff") phase = "idle";
  }

  function closeCurrent() {
    try { window.close(); }
    catch { status("浏览器没有关闭本页，请手动关闭这个旧课程标签页。", true); }
  }

  async function beginHandoff(href, manual = false, kind = "next") {
    if (outgoing || refreshJob || disposed) return;
    if (!runtimeReady) return status(runtimeError || "正在准备刷新计时，请稍候。", true);
    cancelBackground();
    const prompt = blockingPrompt();
    if (prompt) return pause(prompt, "prompt");
    const url = safeUnitUrl(href);
    if (!url) return pause("未找到可确认的单元链接，请手动选择课程。", "timeout");
    if (!hasTabApis()) return pause("请在篡改猴中保存完整的 4.7 脚本，并确认标签页权限。", "permission");
    const attemptTime = Date.now();
    try {
      const stored = GM_getValue(ATTEMPTS_KEY, {});
      const attempts = Object.fromEntries(Object.entries(stored && typeof stored === "object" ? stored : {})
        .filter(([, time]) => Number.isFinite(time) && Date.now() - time < 120_000));
      if (!manual && Object.prototype.hasOwnProperty.call(attempts, routeKey(url))) {
        return pause("本节已尝试重新打开，等待播放器恢复；强制刷新继续计时。", kind === "recover" ? "loading" : "timeout");
      }
      attempts[routeKey(url)] = attemptTime;
      GM_setValue(ATTEMPTS_KEY, attempts);
    } catch { return pause("无法保存标签页切换状态，请检查篡改猴是否正常运行。", "permission"); }
    paused = false;
    phase = "handoff";
    playGeneration++;
    playPending = false;
    const transfer = { created: attemptTime, attemptRoute: routeKey(url), key: "", tab: null, closing: false };
    outgoing = transfer;
    status("正在准备新标签页，旧课程页暂时保留");
    try {
      const fromId = await selfTabId();
      if (outgoing !== transfer || disposed) return;
      const token = crypto.randomUUID();
      transfer.key = TRANSFER_PREFIX + token;
      GM_setValue(transfer.key, { version: 4, fromId, fromUrl: location.href, target: url,
        created: Date.now(), stage: "prepare", kind,
        runtime: { ...structuredClone(runtime), paused: false, pendingRefresh: null,
          resumePlayback: kind === "next" || kind === "manual-reopen" ? true : runtime.resumePlayback } });
      const bridge = new URL("/", location.origin);
      bridge.searchParams.set(BRIDGE_PARAM, token);
      transfer.tab = GM_openInTab(bridge.href, { active: true, insert: true, setParent: false });
      if (!transfer.tab) throw new Error("new tab unavailable");
      appendEvent("handoff-prepare", kind === "next" ? "下一节过渡页已准备，等待关闭旧页" : "本节重开过渡页已准备");
      status("新标签页正在准备，准备完成后才会关闭旧页");
    } catch {
      if (outgoing === transfer) pause("新标签页未能启动，已保留本页。请检查篡改猴权限后继续。", "permission");
    }
  }

  function pollOutgoing() {
    const transfer = outgoing;
    if (!transfer) return;
    if (Date.now() - transfer.created > BRIDGE_TIMEOUT_MS) {
      return pause("新页面接续超时，已停止切换并保留旧页。", "timeout");
    }
    if (!transfer.key) return;
    let record;
    try { record = GM_getValue(transfer.key, null); }
    catch { return pause("无法读取标签页切换状态，已保留本页。", "permission"); }
    if (!record) return pause("新页面接续已取消，旧页已保留。", "timeout");
    if (record.stage === "bridge-ready" && !transfer.closing) {
      transfer.closing = true;
      try { GM_setValue(transfer.key, { ...record, stage: "closing" }); }
      catch { return pause("无法保存关闭旧页的状态，已保留本页。", "permission"); }
      courseVideo()?.pause();
      status("新标签页已准备，正在关闭本页");
      appendEvent("handoff-close", "过渡页确认就绪，关闭旧课程页");
      closeCurrent();
    } else if (transfer.closing) {
      status("如本页未自动关闭，请点“关闭本页并继续”，或手动关闭此旧标签页。", true);
    }
  }

  function startBridge() {
    const key = TRANSFER_PREFIX + bridgeToken;
    let checking = false, checkStarted = 0, absentSince = 0, completed = false;
    function stop(message) {
      completed = true;
      status(message, true);
      if (timer) window.clearInterval(timer);
    }
    function bridgeTick() {
      if (disposed || completed || !panel()) return;
      if (checking) {
        if (Date.now() - checkStarted >= 5_000) stop("确认旧标签页状态超时，请手动重新打开课程。");
        return;
      }
      if (!hasTabApis() || !/^[a-f0-9-]{36}$/i.test(bridgeToken || "")) return stop("接续信息无效，请重新打开课程。");
      let record;
      try { record = GM_getValue(key, null); }
      catch { return stop("无法读取接续信息，请检查篡改猴权限。"); }
      if (!record) return stop("本次切换已取消，请回到原课程标签页。");
      const target = safeUnitUrl(record.target, record.fromUrl);
      if (record.version !== 4 || !target || !record.fromId || !Number.isFinite(record.created) ||
        Date.now() - record.created > BRIDGE_TIMEOUT_MS || Date.now() < record.created) {
        return stop("接续信息已失效，请从课程目录重新进入。");
      }
      if (record.stage === "prepare") {
        try { GM_setValue(key, { ...record, stage: "bridge-ready" }); }
        catch { return stop("无法确认新标签页就绪，请检查篡改猴权限。"); }
        return status("新标签页已准备，正在等待旧课程页关闭");
      }
      if (!["bridge-ready", "closing"].includes(record.stage)) return stop("本次切换已停止。");
      checking = true;
      checkStarted = Date.now();
      try {
        GM_getTabs(tabs => {
          checking = false;
          if (disposed || completed) return;
          // 使用篡改猴的标签页清单确认关闭，不以后台计时器是否跳动来猜测。
          const oldExists = Object.values(tabs || {}).some(tab => tab?.[TAB_FIELD] === record.fromId);
          if (oldExists) {
            absentSince = 0;
            return status("请等待旧课程页关闭；若未自动关闭，请手动关闭旧标签页。");
          }
          if (!absentSince) absentSince = Date.now();
          if (Date.now() - absentSince < RELEASE_DELAY_MS) return status("旧页已关闭，正在等待释放后重新进入课程");
          // 关闭期间若用户取消接续，不能继续导航。
          let latest;
          try { latest = GM_getValue(key, null); }
          catch { return stop("无法读取最新接续状态，已停止打开课程。"); }
          if (!latest || latest.fromId !== record.fromId || latest.target !== record.target) return stop("本次切换已取消。");
          completed = true;
          window.clearInterval(timer);
          runtime = normalizeRuntime(record.runtime, target);
          const timerWasDue = runtime.enabled && Date.now() >= runtime.nextAt;
          if (timerWasDue) {
            runtime.nextAt = Date.now() + REFRESH_MS;
            runtime.pendingRefresh = { id: crypto.randomUUID(), documentId: DOCUMENT_ID,
              route: routeKey(target), kind: "periodic", at: Date.now() };
          } else if (record.kind === "manual-reopen") runtime.nextAt = Date.now() + REFRESH_MS;
          // 把同一条十分钟计时保存到新标签页，不能在每次短视频切课时重新开始。
          void persistRuntime().then(() => {
            if (disposed) return;
            const active = GM_getValue(key, null);
            if (!active || active.fromId !== record.fromId || active.target !== record.target) return stop("本次切换已取消。");
            appendEvent("handoff-open", timerWasDue ? "十分钟到期，随接续页面加载执行刷新" : "旧页已关闭，在新标签页进入课程", target);
            status("正在重新打开课程");
            location.replace(target);
            GM_deleteValue(key);
          }).catch(() => stop("保存新页面计时失败，请从课程目录重新进入。"));
        });
      } catch { checking = false; stop("无法确认旧标签页是否关闭，请手动重新打开课程。"); }
    }
    timer = window.setInterval(bridgeTick, 500);
    bridgeTick();
  }

  function startWaiting(video) {
    if (refreshJob) return;
    cancelBackground();
    endedRecord = { video, source: source(video), route: routeKey(), time: Date.now() };
    phase = "waiting";
    deadline = Date.now() + WAIT_MS;
    wantPlay = false;
    playGeneration++;
    playPending = false;
    needsGesture = false;
    status("本节已结束，等待平台显示“下一单元”");
    appendEvent("video-ended", "本节自然播放结束，等待下一单元");
  }

  function onEnded(event) {
    if (paused || refreshJob || !onCoursePage() || phase !== "idle") return;
    const video = event.target;
    if (!(video instanceof HTMLVideoElement) || video !== courseVideo() || !video.ended) return;
    const prompt = blockingPrompt();
    if (prompt) return pause(prompt, "prompt");
    startWaiting(video);
  }

  function resetForVideo(video) {
    activeKey = mediaKey(video);
    endedRecord = null;
    phase = "idle";
    wantPlay = restoreIntent === null ? true : restoreIntent;
    restoreIntent = null;
    needsGesture = !wantPlay;
    backgroundWanted = wantPlay;
    nextPlayAt = 0;
    playGeneration++;
    playPending = false;
    installMediaControls();
    status(wantPlay ? "已识别本节视频，准备播放" : "页面已恢复，保留本节原来的暂停状态。可点“播放本节”。");
  }

  function play(video, userGesture = false) {
    if (paused || !video || video.ended || !wantPlay || playPending ||
      (!userGesture && (needsGesture || video.readyState < 2 || Date.now() < nextPlayAt))) return;
    if (!video.paused) {
      wantPlay = false;
      needsGesture = false;
      status("正在播放，本节结束后自动进入下一单元");
      return;
    }
    const generation = ++playGeneration;
    const key = mediaKey(video);
    playPending = true;
    playDeadline = Date.now() + WAIT_MS;
    status("正在启动本节视频");
    const failed = error => {
      if (generation !== playGeneration || paused || key !== mediaKey(video)) return;
      playPending = false;
      if (error?.name === "AbortError") {
        nextPlayAt = Date.now() + 1_000;
        status("播放器正在加载，稍后重新尝试播放");
      } else {
        needsGesture = true;
        status(error?.name === "NotAllowedError"
          ? "浏览器拦截了自动播放，请点下方“播放本节”。"
          : "播放器未能启动，请点“播放本节”或页面播放键。", true);
      }
    };
    try {
      Promise.resolve(video.play()).then(() => {
        if (generation !== playGeneration || paused || key !== mediaKey(video)) return;
        playPending = false;
        wantPlay = false;
        needsGesture = false;
        status("正在播放，本节结束后自动进入下一单元");
      }, failed);
    } catch (error) { failed(error); }
  }

  function isBackground() {
    return document.visibilityState === "hidden" || !document.hasFocus();
  }

  function cancelBackground() {
    backgroundJob = null;
    backgroundProof = null;
  }

  function scheduleBackground(video) {
    if (backgroundJob || !runtime?.backgroundEnabled || !runtime.resumePlayback || !backgroundWanted ||
      paused || outgoing || refreshJob || phase !== "idle" || !video?.paused || video.ended) return;
    if (document.pictureInPictureElement === video) return;
    backgroundJob = { video, key: mediaKey(video), readyAt: Date.now() + 250 };
  }

  function pollBackground() {
    const job = backgroundJob;
    if (!job || Date.now() < job.readyAt) return;
    backgroundJob = null;
    const video = courseVideo();
    if (!video || video !== job.video || mediaKey(video) !== job.key || !video.paused || video.ended ||
      !runtime.backgroundEnabled || !runtime.resumePlayback || !backgroundWanted || paused || outgoing || refreshJob) return;
    const prompt = blockingPrompt();
    if (prompt) return pause(prompt, "prompt");
    backgroundAttempts = backgroundAttempts.filter(time => Date.now() - time < 15_000);
    if (backgroundAttempts.length >= 3) {
      needsGesture = true;
      return status("后台恢复连续失败，已停止重试。请回到课程页点“播放本节”。", true);
    }
    backgroundAttempts.push(Date.now());
    backgroundProof = { key: job.key, from: video.currentTime };
    wantPlay = true;
    needsGesture = false;
    appendEvent("background-resume", "切换到后台后恢复实际播放");
    play(video);
  }

  function onPageActivity() {
    if (!runtimeReady || disposed || paused || outgoing || refreshJob || phase !== "idle") return;
    const video = courseVideo();
    if (!video || video.ended || !runtime.backgroundEnabled) return;
    if (!isBackground()) backgroundAttempts = [];
    if (!video.paused) {
      backgroundWanted = true;
      if (!runtime.resumePlayback) { runtime = { ...runtime, resumePlayback: true }; saveRuntimeInBackground(); }
      if (isBackground()) backgroundProof = { key: mediaKey(video), from: video.currentTime };
      status(isBackground() ? "正在后台播放，本节结束后自动连播" : "正在播放，本节结束后自动连播");
    } else if (runtime.resumePlayback && backgroundWanted) scheduleBackground(video);
  }

  function installMediaControls() {
    if (mediaSessionInstalled || !navigator.mediaSession?.setActionHandler) return;
    try {
      navigator.mediaSession.setActionHandler("pause", () => {
        backgroundWanted = false;
        cancelBackground();
        wantPlay = false;
        if (runtimeReady) { runtime = { ...runtime, resumePlayback: false }; saveRuntimeInBackground(); }
        courseVideo()?.pause();
        status("已通过媒体控制手动暂停播放");
      });
      navigator.mediaSession.setActionHandler("play", () => {
        const video = courseVideo();
        if (!video) return;
        backgroundWanted = true;
        wantPlay = true;
        needsGesture = false;
        if (paused) { void video.play().catch(() => {}); return; }
        play(video, true);
      });
      mediaSessionInstalled = true;
    } catch {}
  }

  function onMediaPlayback(event) {
    if (!runtimeReady || disposed || paused || outgoing || refreshJob || phase !== "idle") return;
    const video = event.target;
    if (!(video instanceof HTMLVideoElement) || video !== courseVideo() || video.ended) return;
    if (event.type === "timeupdate") {
      const key = mediaKey(video);
      if (backgroundProof && backgroundProof.key === key && !video.paused && isBackground() &&
        video.currentTime - backgroundProof.from >= 1) {
        appendEvent("background-playing", `已确认后台播放，视频进度前进 ${Math.floor(video.currentTime - backgroundProof.from)} 秒`);
        backgroundProof = null;
      }
      if (!video.paused && video.currentTime > 1 && lastPlayingKey !== key) {
        lastPlayingKey = key;
        appendEvent("playing", "视频已实际开始播放");
      }
      return;
    }
    if (event.type === "pause" && runtime.backgroundEnabled && isBackground() &&
      (runtime.resumePlayback || backgroundWanted) && document.pictureInPictureElement !== video) {
      backgroundWanted = true;
      scheduleBackground(video);
      status("页面已转到后台，正在保持视频播放");
      return;
    }
    if (playPending && event.type === "pause") return;
    const intended = event.type === "play";
    backgroundWanted = intended;
    if (intended && isBackground()) backgroundProof = { key: mediaKey(video), from: video.currentTime };
    if (!intended) cancelBackground();
    if (runtime.resumePlayback !== intended) {
      runtime = { ...runtime, resumePlayback: intended };
      saveRuntimeInBackground();
    }
    status(intended ? (isBackground() ? "正在后台播放，本节结束后自动连播" : "正在播放，本节结束后自动连播")
      : "本节视频已暂停；定时刷新仍按计划计时。");
  }

  function tick() {
    if (!onCoursePage()) {
      if (host) host.style.setProperty("display", "none", "important");
      if (activeKey || endedRecord) {
        phase = "idle";
        activeKey = "";
        endedRecord = null;
        playGeneration++;
        playPending = false;
      }
      return;
    }
    if (!panel()) return;
    host.style.setProperty("display", "block", "important");
    renderClock();
    if (!runtimeReady) return status(runtimeError || "正在读取十分钟刷新计时", Boolean(runtimeError));
    if (refreshJob) {
      if (Date.now() - refreshJob.at >= WAIT_MS) retryRefresh();
      return;
    }
    // 独立于播放器、弹窗、连播暂停和切课状态，计时到期即刷新。
    if (runtime.enabled && Date.now() >= runtime.nextAt) { void requestRefresh(); return; }
    pollSpeed(courseVideo());
    if (paused) {
      // 加载超时只阻止重复开页。平台稍后成功生成播放器时，继续跟踪自然结束。
      // 用户暂停、验证等待及下一节歧义等状态仍由各自的处理入口控制。
      const recovered = pauseReason === "loading" && phase === "idle" && courseVideo();
      if (!recovered || !source(recovered) || recovered.readyState < 1 ||
        (recovered.paused && !recovered.ended) || blockingPrompt()) return;
      paused = false;
      pauseReason = "";
      loadingSince = 0;
      appendEvent("player-recovered", "播放器已恢复，自动继续连播；刷新计时保持不变");
      status(recovered.ended ? "播放器已恢复，正在衔接下一单元" : "播放器已恢复，已继续连播");
    }
    const prompt = blockingPrompt();
    if (prompt) return pause(prompt, "prompt");
    if (outgoing) return pollOutgoing();
    const video = courseVideo();

    if (endedRecord) {
      const routeChanged = routeKey() !== endedRecord.route;
      // 平台倒计时可能先改地址；仍按“关旧页后重开”接续当前目标。
      if (routeChanged) { void beginHandoff(location.href); return; }
    } else if (video && source(video) && video.readyState >= 1 && mediaKey(video) !== activeKey) {
      resetForVideo(video);
    }

    if (phase === "waiting") {
      if (Date.now() - endedRecord.time < SETTLE_MS) return;
      const endPanel = [...document.querySelectorAll('[class*="modal_mark___"]')].find(visible);
      if (endPanel && /已经是最后一个单元了|已是最后一(?:节|课)/.test(endPanel.innerText || endPanel.textContent || "")) {
        phase = "done";
        return status("本课程已播放到最后一个单元。");
      }
      const controls = nextControls();
      if (controls.length > 1) return pause("发现多个下一节入口，请检查后点“继续连播”。", "ambiguous");
      if (controls.length === 1 && enabled(controls[0])) {
        const targetUrl = nextUnitUrl(controls[0]);
        if (!targetUrl) return pause("无法唯一确认下一节的目录链接，已停止切换，请手动选择。", "ambiguous");
        void beginHandoff(targetUrl);
        return;
      }
      if (Date.now() >= deadline) return pause("30 秒内没找到可用的下一单元按钮，请检查后继续。", "timeout");
      return status("等待平台的“下一单元”或倒计时按钮");
    }
    if (phase === "done") {
      if (video && !video.ended && mediaKey(video) === activeKey) resetForVideo(video);
      else return;
    }
    if (!video || !source(video) || video.readyState < 1) {
      if (!loadingSince) loadingSince = Date.now();
      if (Date.now() - loadingSince >= WAIT_MS) { void beginHandoff(location.href, false, "recover"); return; }
      return status("等待本节播放器初始化；持续未加载时会尝试关闭旧页后重开。", true);
    }
    loadingSince = 0;
    if (video.ended) return startWaiting(video); // 安装脚本时已结束，也能接上。
    if (backgroundJob) {
      pollBackground();
      if (backgroundJob || paused) return;
    }
    if (!video.paused && (wantPlay || needsGesture)) {
      wantPlay = false;
      needsGesture = false;
      playGeneration++;
      playPending = false;
      return status("正在播放，本节结束后自动进入下一单元");
    }
    if (playPending && Date.now() >= playDeadline) {
      playGeneration++;
      playPending = false;
      needsGesture = true;
      return status("启动播放等待超时，请点“播放本节”检查。", true);
    }
    play(video);
  }

  window[INSTANCE] = { destroy() {
    disposed = true;
    cancelOutgoing();
    cancelRefresh();
    cancelBackground();
    window.clearInterval(timer);
    document.removeEventListener("ended", onEnded, true);
    for (const name of ["play", "pause", "timeupdate"]) document.removeEventListener(name, onMediaPlayback, true);
    document.removeEventListener("visibilitychange", onPageActivity, true);
    for (const name of ["loadeddata", "playing", "ratechange", "timeupdate"]) document.removeEventListener(name, onSpeedEvent, true);
    for (const name of ["click", "pointerdown", "keydown"]) document.removeEventListener(name, onPlayerSpeedInput, true);
    for (const name of ["blur", "focus"]) window.removeEventListener(name, onPageActivity, true);
    if (mediaSessionInstalled) { try { navigator.mediaSession.setActionHandler("pause", null); navigator.mediaSession.setActionHandler("play", null); } catch {} }
    playGeneration++;
    host?.remove();
  } };
  if (bridgeToken) startBridge();
  else {
    document.addEventListener("ended", onEnded, true);
    for (const name of ["play", "pause", "timeupdate"]) document.addEventListener(name, onMediaPlayback, true);
    document.addEventListener("visibilitychange", onPageActivity, true);
    for (const name of ["loadeddata", "playing", "ratechange", "timeupdate"]) document.addEventListener(name, onSpeedEvent, true);
    for (const name of ["click", "pointerdown", "keydown"]) document.addEventListener(name, onPlayerSpeedInput, true);
    for (const name of ["blur", "focus"]) window.addEventListener(name, onPageActivity, true);
    timer = window.setInterval(tick, 500);
    runtimeInit = initializeRuntime().catch(() => {
      if (disposed) return;
      runtimeError = "无法初始化刷新计时。请在篡改猴中保存完整的 4.7 脚本及权限声明后重新打开课程。";
      paused = true;
      status(runtimeError, true);
    });
    tick();
  }
})();
