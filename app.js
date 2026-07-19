// Budgetify - Application Logic (app.js)

// --- CONFIG & STATE ---
const CONFIG = {
    storageKey: 'budgetify_db_perpetual',
    taxRate: 0.20 // 20% tax savings on side gigs
};

let state = {
    currentYear: 2026,
    currentMonth: 'Jul', // 'Jan', 'Feb', ..., 'Dec'
    selectedDate: null,   // 'YYYY-MM-DD'
    deliveryWeekIndex: 0, // index of current delivery week (0 to 4/5)
    deliveryEarnings: [],
    deliveryBudgets: {},
    taxSavings: [],
    jointRegister: [],
    monthlyBills: {},
    manualTransfers: [],
    personalCalendar: {},
    loans: [],
    dashboardType: 'personal', // 'personal' or 'joint'
    viewMode: 'calendar',       // 'calendar' or 'list'
    listScope: 'month',         // 'month' or 'year'
    savingsCurrentAmount: 0,
    savingsStartingBalance: 0,
    savingsTransactions: [],
    savingsViewMode: 'calendar',
    savingsListScope: 'month',
    savingsMetricsCollapsed: false,
    savingsYearSummaryCollapsed: false,
    deliveryYearSummaryCollapsed: false
};

// Parser to map Joint Register preloaded items with appropriate calendar dates
function assignDatesToJointRegister(jointRegister) {
    const monthMap = {
        Jan: '01', Feb: '02', Mar: '03', Apr: '04', May: '05', Jun: '06',
        Jul: '07', Aug: '08', Sep: '09', Oct: '10', Nov: '11', Dec: '12',
        April: '04', June: '06', July: '07', August: '08', September: '09',
        October: '10', November: '11', December: '12'
    };
    let currentDate = '2027-01-01';
    return jointRegister.map(item => {
        if (item.type === 'contribution') {
            const parts = item.name.split(' ');
            const rawMonth = parts[0];
            const rawDay = parts[1];
            const mm = monthMap[rawMonth] || '01';
            const dd = rawDay === '1st' ? '01' : '15';
            currentDate = `2027-${mm}-${dd}`;
        }
        return { ...item, date: item.date || currentDate };
    });
}

// Default Loans (since spreadsheet only lists monthly payment rows, we seed starting/current balances)
const DEFAULT_LOANS = [
    { id: 'discover_card', name: 'Discover Card', startBal: 5000, currentBal: 2450, monthlyMin: 75, type: 'credit', interestRate: 22.9, dueDay: 10, limit: 10000, promos: [] },
    { id: 'upstart', name: 'Remodel Loan (Upstart)', startBal: 12000, currentBal: 8450, monthlyMin: 338, type: 'loan', interestRate: 7.9, dueDay: 15, limit: 12000, promos: [] },
    { id: 'greensky', name: 'Greensky (Slab Leak)', startBal: 5000, currentBal: 2795, monthlyMin: 215, type: 'loan', interestRate: 0, dueDay: 5, limit: 5000, promos: [] },
    { id: 'bathroom', name: 'Bathroom Remodel (Service Finance)', startBal: 15000, currentBal: 10800, monthlyMin: 285, type: 'loan', interestRate: 5.9, dueDay: 20, limit: 15000, promos: [] },
    { id: 'lightstream', name: 'Lightstream (Floors)', startBal: 12000, currentBal: 7420, monthlyMin: 290, type: 'loan', interestRate: 6.5, dueDay: 18, limit: 12000, promos: [] },
    { id: 'federal_loans', name: 'Federal Student Loans', startBal: 45000, currentBal: 32400, monthlyMin: 675, type: 'loan', interestRate: 4.5, dueDay: 25, limit: 45000, promos: [] },
    { id: 'texas_loans', name: 'Texas Student Loans', startBal: 18000, currentBal: 11200, monthlyMin: 250, type: 'loan', interestRate: 5.0, dueDay: 22, limit: 18000, promos: [] },
    { id: 'disneyland', name: 'Disneyland Trip Payoff', startBal: 4000, currentBal: 2600, monthlyMin: 200, type: 'loan', interestRate: 0, dueDay: 15, limit: 4000, promos: [] }
];

const MONTH_NAMES = {
    Jan: 'January', Feb: 'February', Mar: 'March', Apr: 'April', May: 'May', Jun: 'June',
    Jul: 'July', Aug: 'August', Sep: 'September', Oct: 'October', Nov: 'November', Dec: 'December'
};

const MONTH_ORDER = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];

// Escapes a value for safe interpolation into innerHTML template literals (text content or quoted attributes).
function escapeHTML(value) {
    return String(value ?? '').replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[char]));
}

function shiftCalendarPeriod(year, month, offset) {
    const date = new Date(year, MONTH_ORDER.indexOf(month) + offset, 1);
    return { year: date.getFullYear(), month: MONTH_ORDER[date.getMonth()] };
}

// Helper to calculate bi-weekly paycheck dates in a given year
// Cache for getPaycheckDatesForYear/getPersonalTransactionsForPeriod/getCalculatedTransferForJason/
// getCalculatedTransferForAsia, keyed by year or "year-month"/"year-month-cycle". These are called
// repeatedly (often for every past month in history) from getPersonalRunningBalanceAtDate and
// getJointRunningBalanceAtDate, so an uncached implementation re-derives the same month's paychecks,
// delivery weeks, and bill allocations over and over. Cleared in saveDatabase().
let _paycheckDatesCache = {};
let _personalTxPeriodCache = {};
let _transferForJasonCache = {};
let _transferForAsiaCache = {};

function getPaycheckDatesForYear(year) {
    if (_paycheckDatesCache[year]) return _paycheckDatesCache[year];
    const dates = [];
    const cfg = state.payrollConfig;
    if (!cfg || !cfg.firstPayDate) return dates;
    
    // Parse firstPayDate
    let current = new Date(cfg.firstPayDate + 'T12:00:00Z');
    // Determine the year of the firstPayDate
    const startYear = current.getUTCFullYear();
    
    // Shift current to the target year
    if (startYear > year) {
        while (current.getUTCFullYear() > year) {
            current.setUTCDate(current.getUTCDate() - 14);
        }
    } else if (startYear < year) {
        while (current.getUTCFullYear() < year) {
            current.setUTCDate(current.getUTCDate() + 14);
        }
    }
    
    // Back up to make sure we don't miss the first paychecks of the year
    while (current.getUTCFullYear() === year) {
        current.setUTCDate(current.getUTCDate() - 14);
    }
    current.setUTCDate(current.getUTCDate() + 14);
    
    // Collect all paychecks falling in the target year
    while (current.getUTCFullYear() === year) {
        const yyyy = current.getUTCFullYear();
        const mm = String(current.getUTCMonth() + 1).padStart(2, '0');
        const dd = String(current.getUTCDate()).padStart(2, '0');
        dates.push(`${yyyy}-${mm}-${dd}`);
        current.setUTCDate(current.getUTCDate() + 14);
    }

    _paycheckDatesCache[year] = dates;
    return dates;
}

// Helper to compute Jason's paycheck amount for a specific paycheck date
function getJasonPayrollAmount(year, monthShort, dateStr) {
    const cfg = state.payrollConfig;
    if (!cfg) return 0;
    
    // 1. Get all paycheck dates in the target month to identify index (1st, 2nd, 3rd)
    const yearPaychecks = getPaycheckDatesForYear(year);
    const monthIndex = MONTH_ORDER.indexOf(monthShort);
    const mmStr = String(monthIndex + 1).padStart(2, '0');
    const prefix = `${year}-${mmStr}-`;
    const monthPaychecks = yearPaychecks.filter(d => d.startsWith(prefix)).sort();
    
    const paycheckIdx = monthPaychecks.indexOf(dateStr);
    if (paycheckIdx === -1) return 0; // Not a paycheck day!
    
    // 2. Resolve base pay rate for this paycheck index
    let basePay = 0;
    if (cfg.hasDifferentRates && cfg.differentRates) {
        if (paycheckIdx === 0) basePay = Number(cfg.differentRates.rate1st) || 0;
        else if (paycheckIdx === 1) basePay = Number(cfg.differentRates.rate2nd) || 0;
        else basePay = Number(cfg.differentRates.rate3rd) || 0;
    } else {
        basePay = Number(cfg.baseNetPay) || 0;
        if (paycheckIdx === 0) {
            basePay += Number(cfg.stipendAmount) || 0;
        }
    }
    
    // 3. Apply active estimates (increases) chronologically
    const sortedEstimates = (cfg.estimates || []).map(est => {
        return {
            ...est,
            monthIdx: MONTH_ORDER.indexOf(est.effectiveMonth)
        };
    }).sort((a, b) => {
        if (a.effectiveYear !== b.effectiveYear) return a.effectiveYear - b.effectiveYear;
        return a.monthIdx - b.monthIdx;
    });
    
    let rate = basePay;
    const targetMonthIdx = MONTH_ORDER.indexOf(monthShort);
    
    sortedEstimates.forEach(est => {
        let triggers = 0;
        if (year > est.effectiveYear || (year === est.effectiveYear && targetMonthIdx >= est.monthIdx)) {
            if (est.isRecurring) {
                const yearsDiff = year - est.effectiveYear;
                if (targetMonthIdx < est.monthIdx) {
                    triggers = yearsDiff;
                } else {
                    triggers = yearsDiff + 1;
                }
            } else {
                triggers = 1;
            }
        }
        
        if (triggers > 0) {
            if (est.type === 'percent') {
                rate = rate * Math.pow(1 + (Number(est.value) || 0) / 100, triggers);
            } else {
                // Preserve an explicit 0 (e.g. an unpaid-leave estimate) instead of falling back
                // to the previous rate, which only `Number(est.value) || rate` would have done.
                rate = (est.value === '' || est.value === null || est.value === undefined || Number.isNaN(Number(est.value)))
                    ? rate
                    : Number(est.value);
            }
        }
    });
    
    return rate;
}

// Helper to get weeks (Mon-Sun) whose Sunday falls within a given month
function getWeeksForMonth(year, monthShort) {
    const monthIndex = MONTH_ORDER.indexOf(monthShort);
    if (monthIndex < 0) return [];
    
    const sundays = [];
    const lastOfMonth = new Date(year, monthIndex + 1, 0);
    for (let d = 1; d <= lastOfMonth.getDate(); d++) {
        const date = new Date(year, monthIndex, d);
        if (date.getDay() === 0) { // Sunday
            sundays.push(new Date(date));
        }
    }
    
    const weeks = [];
    sundays.forEach(sunDate => {
        const week = [];
        for (let i = -6; i <= 0; i++) {
            const dayDate = new Date(sunDate);
            dayDate.setDate(sunDate.getDate() + i);
            week.push(ensureDeliveryEarningForDate(dayDate));
        }
        weeks.push(week);
    });
    return weeks;
}

// Helper to get personal checking register transactions for a period, injecting dynamic paychecks and filtering static ones
function getPersonalTransactionsForPeriod(year, monthShort) {
    const key = `${year}-${monthShort}`;
    if (_personalTxPeriodCache[key]) return _personalTxPeriodCache[key];
    const rawList = state.personalCalendar[key] || [];
    
    // 1. Filter out static "Payday" transactions (where description === 'Payday' and it does not have a valid id)
    let filteredList = rawList.filter(tx => !tx.billOccurrenceDeleted && !(tx.description === 'Payday' && (!tx.id || tx.id.startsWith('payday-temp-'))));
    
    // 2. Dynamically generate and inject paychecks for this period
    const yearPaychecks = getPaycheckDatesForYear(year);
    const monthIndex = MONTH_ORDER.indexOf(monthShort);
    const mmStr = String(monthIndex + 1).padStart(2, '0');
    const prefix = `${year}-${mmStr}-`;
    const skippedPaychecks = state.payrollConfig?.skippedPaychecks || [];
    const monthPaychecks = yearPaychecks.filter(d => d.startsWith(prefix) && !skippedPaychecks.includes(d));
    
    monthPaychecks.forEach(dateStr => {
        const id = `dynamic-paycheck-${dateStr}`;
        const override = (state.dynamicOverrides || {})[id];
        if (override?.deleted) return;

        const calculatedAmount = getJasonPayrollAmount(year, monthShort, dateStr);
        const amount = override?.amount !== undefined
            ? Math.abs(Number(override.amount) || 0)
            : calculatedAmount;
        if (amount > 0) {
            filteredList.push({
                id,
                date: dateStr,
                description: override?.description || 'Jason Pay (Dynamic)',
                amount,
                isSplitterDynamic: true
            });
        }
    });
    
    // 3. Dynamically generate and inject delivery earnings on Sundays
    const monthWeeks = getWeeksForMonth(year, monthShort);
    monthWeeks.forEach(week => {
        let weekGrossTotal = 0;
        let allActualized = true;
        
        week.forEach(gRecord => {
            const isActualized = !!(gRecord.offDayReason || gRecord.total > 0 || gRecord.noEarnCash || gRecord.noEarnSideGigs || gRecord.noEarnGrubHub || gRecord.noEarnUberEats);
            if (!isActualized) {
                allActualized = false;
            }
            
            if (gRecord.offDayReason) {
                // Off day: contribution is 0
            } else if (isActualized) {
                weekGrossTotal += gRecord.total;
            } else {
                weekGrossTotal += Number(state.deliveryBudgets?.[gRecord.date]) || 0;
            }
        });
        
        if (weekGrossTotal > 0) {
            const sundayDateStr = week[6].date;
            const id = `dynamic-delivery-${sundayDateStr}`;
            
            // Check if there is a deletion override
            const override = (state.dynamicOverrides || {})[id];
            if (override?.deleted) return;
            
            filteredList.push({
                id,
                date: sundayDateStr,
                description: override?.description || (allActualized ? 'Delivery Earnings (Actual)' : 'Delivery Earnings (Proj)'),
                amount: override?.amount !== undefined ? Math.abs(Number(override.amount) || 0) : weekGrossTotal,
                isSplitterDynamic: true
            });
        }
    });

    _personalTxPeriodCache[key] = filteredList;
    return filteredList;
}

function renderPayrollEstimatesList() {
    const listContainer = document.getElementById('payroll-est-list');
    if (!listContainer) return;
    
    listContainer.innerHTML = '';
    const estimates = state.payrollConfig.estimates || [];
    
    if (estimates.length === 0) {
        listContainer.innerHTML = '<p class="muted-text" style="grid-column: 1 / -1; text-align: center; font-size: 0.85rem; padding: 0.5rem;">No projected pay increases added yet.</p>';
        return;
    }
    
    estimates.forEach(est => {
        const item = document.createElement('div');
        item.style = 'display: flex; justify-content: space-between; align-items: center; background: rgba(255,255,255,0.05); padding: 6px 12px; border-radius: 6px; font-size: 0.85rem;';
        
        const typeStr = est.type === 'percent' ? `${est.value}% Increase` : `+$${est.value} Fixed`;
        const recurStr = est.isRecurring ? ' (Recurring YoY)' : '';
        item.innerHTML = `
            <span><strong>${MONTH_NAMES[est.effectiveMonth]} ${est.effectiveYear}</strong>: ${typeStr}${recurStr}</span>
            <button type="button" class="action-btn small-btn danger-btn delete-est-btn" data-id="${est.id}" style="padding: 2px 6px; font-size: 0.75rem;">Delete</button>
        `;
        
        item.querySelector('.delete-est-btn').addEventListener('click', (e) => {
            const id = e.currentTarget.dataset.id;
            state.payrollConfig.estimates = state.payrollConfig.estimates.filter(item => item.id !== id);
            saveDatabase();
            renderPayrollEstimatesList();
        });
        
        listContainer.appendChild(item);
    });
}

// --- INITIALIZATION ---
function init() {
    loadDatabase();
    setupEventListeners();
    
    // Sync state selectors
    document.getElementById('year-select').value = state.currentYear;
    document.getElementById('month-select').value = state.currentMonth;
    
    // Sync date picker to selectedDate or today (local calendar date, not UTC — toISOString()
    // would shift to the wrong day for users east of UTC in the morning or west of UTC at night).
    const todayStr = formatLocalDate(new Date());

    state.selectedDate = state.selectedDate || todayStr;
    document.getElementById('trans-date').value = state.selectedDate;
    
    // Set UI states for segmented controls
    updateSegmentedControlsUI();
    
    // Ensure active month and delivery logs are initialized
    ensureYearMonthInitialized(state.currentYear, state.currentMonth);
    ensureDeliveryEarningsForMonth(state.currentYear, state.currentMonth);
    reconcileCardCurrentBalances();
    
    setupCCDashboardListeners();
    setupInlineAutocomplete('trans-desc', 'checking-description-suggestions');
    setupInlineAutocomplete('edit-tx-desc', 'checking-description-suggestions');
    renderApp();
    logSystem(`Application initialized. Switched to ${MONTH_NAMES[state.currentMonth]} ${state.currentYear}.`);
}

// Checks the shape of a parsed backup file before it's allowed to replace the live database.
// Returns a human-readable reason string if the file is unsafe to load, or null if it looks fine.
// This only checks structure (right types in the right places), not business-rule correctness —
// its job is to stop a malformed file from getting saved to localStorage and crashing the app on
// the next reload, not to fully validate every field.
function validateImportedDatabase(data) {
    if (!data || typeof data !== 'object' || Array.isArray(data)) return "File does not contain a budget database object.";
    if (!Array.isArray(data.deliveryEarnings)) return "Missing or invalid 'deliveryEarnings' list.";
    if (!data.monthlyBills || typeof data.monthlyBills !== 'object' || Array.isArray(data.monthlyBills)) return "Missing or invalid 'monthlyBills' data.";

    const isPlainObject = (value) => !!value && typeof value === 'object' && !Array.isArray(value);

    if (data.personalCalendar !== undefined) {
        if (!isPlainObject(data.personalCalendar)) return "'personalCalendar' must be an object of date-keyed transaction lists.";
        for (const [key, txList] of Object.entries(data.personalCalendar)) {
            if (!Array.isArray(txList)) return `'personalCalendar.${key}' must be a list of transactions.`;
        }
    }
    if (data.jointRegister !== undefined && !Array.isArray(data.jointRegister)) return "'jointRegister' must be a list.";
    if (data.loans !== undefined && !Array.isArray(data.loans)) return "'loans' must be a list.";
    if (data.savingsTransactions !== undefined && !Array.isArray(data.savingsTransactions)) return "'savingsTransactions' must be a list.";
    if (data.manualTransfers !== undefined && !Array.isArray(data.manualTransfers)) return "'manualTransfers' must be a list.";
    if (data.seasonalExpenses !== undefined && !Array.isArray(data.seasonalExpenses)) return "'seasonalExpenses' must be a list.";
    if (data.cardCalendars !== undefined) {
        if (!isPlainObject(data.cardCalendars)) return "'cardCalendars' must be an object of card ledgers.";
        for (const [cardId, monthMap] of Object.entries(data.cardCalendars)) {
            if (!isPlainObject(monthMap)) return `'cardCalendars.${cardId}' must be an object of date-keyed transaction lists.`;
            for (const [key, txList] of Object.entries(monthMap)) {
                if (!Array.isArray(txList)) return `'cardCalendars.${cardId}.${key}' must be a list of transactions.`;
            }
        }
    }
    return null;
}

// Load from localStorage or global backup from initial_data.js
function loadDatabase() {
    let cached = localStorage.getItem(CONFIG.storageKey);
    if (!cached) {
        // Try importing legacy data from old key
        const legacyCached = localStorage.getItem('budgetify_db_2027');
        if (legacyCached) {
            cached = legacyCached;
            localStorage.removeItem('budgetify_db_2027');
            console.log("Imported legacy database from budgetify_db_2027.");
        }
    }
    
    if (cached) {
        try {
            state = JSON.parse(cached);
            migrateDatabase();
        } catch (e) {
            console.error("Failed to parse cached DB, resetting to defaults", e);
            // Preserve the unreadable data under a separate key instead of discarding it outright,
            // so it isn't unrecoverably lost if this was a one-off parse error rather than real corruption.
            try { localStorage.setItem(CONFIG.storageKey + '_corrupted_backup_' + Date.now(), cached); } catch (storageErr) { /* ignore quota errors */ }
            alert("Your saved budget data could not be loaded and appears to be corrupted, so the app has been reset to default data. The unreadable data was preserved in a separate localStorage entry for recovery.");
            resetToDefaults();
        }
    } else {
        resetToDefaults();
    }
}

// The actual localStorage write is debounced (cache invalidation below still happens synchronously
// on every call, so nothing else observes stale data). Two reasons: (1) the background month prewarm
// can call saveDatabase() up to ~30 times in a burst — one .setItem() per month materialized — and
// each one serializes the *entire* app state, which is wasted work when only the trailing state
// actually needs to land on disk; (2) mobile browsers (especially Safari in a third-party iframe, e.g.
// Google Sites' embed) often have much smaller/stricter storage quotas and can throw or stall on
// frequent large writes — collapsing ~30 writes into 1 meaningfully reduces how often that's hit.
// flushPendingSave() is called on beforeunload so a page close can't drop the last edit.
let _pendingSaveTimer = null;
function flushPendingSave() {
    if (_pendingSaveTimer === null) return;
    clearTimeout(_pendingSaveTimer);
    _pendingSaveTimer = null;
    try {
        localStorage.setItem(CONFIG.storageKey, JSON.stringify(state));
    } catch (e) {
        // Quota exceeded or storage blocked (common in mobile/embedded-iframe contexts) — the app
        // should keep running on its in-memory state rather than crash whatever caller triggered
        // this save, which previously could leave the busy overlay stuck forever with no error shown.
        console.warn('Failed to persist to localStorage (continuing without saving):', e);
    }
}
window.addEventListener('beforeunload', flushPendingSave);

function saveDatabase() {
    clearTimeout(_pendingSaveTimer);
    _pendingSaveTimer = setTimeout(flushPendingSave, 250);
    _adjustedTransferCache = {};
    _deliveryEarningsIndex = null;
    _cardBalanceEstimatesCache = {};
    _paycheckDatesCache = {};
    _personalTxPeriodCache = {};
    _transferForJasonCache = {};
    _transferForAsiaCache = {};
    _personalRunningBalanceCache = {};
    _jointRunningBalanceCache = {};
    _sortedPersonalCalendarKeysCache = null;
    _personalMonthFullContributionCache = { true: {}, false: {} };
    _personalMonthStartCheckpointCache = { true: {}, false: {} };
    _jointRegisterSortedCache = null;
    _jointMonthFullContributionCache = {};
    _jointDynamicCheckpointCache = {};
    // Deliberately NOT bumping _prewarmGeneration here. A prewarm step can itself trigger a real
    // saveDatabase() (e.g. ensureAutomaticCardPaymentForMonth creating a loan's first payment when a
    // never-before-seen month is initialized) — bumping the generation from inside saveDatabase() used
    // to make the chain invalidate itself on its own very first internal save and never resume. Actual
    // user edits still supersede any in-flight chain correctly: they're followed by renderApp(), which
    // calls queuePrewarmForCurrentMonth() and increments the generation there.
}

// Keep the card summary balance in sync with its calendar ledger.
// Calendar charges are stored as negative amounts; payments are positive.
function adjustCardCurrentBalance(cardId, transactionAmount, direction = 1) {
    const card = state.loans.find(loan => loan.id === cardId);
    if (!card || !Number.isFinite(transactionAmount)) return;

    const balanceEffect = transactionAmount < 0
        ? Math.abs(transactionAmount)
        : -Math.abs(transactionAmount);

    card.currentBal = Math.max(0, (Number(card.currentBal) || 0) + (balanceEffect * direction));
}

function sanitizeStoredEncoding(value, seen = new WeakSet()) {
    if (!value || typeof value !== 'object' || seen.has(value)) return 0;
    seen.add(value);
    let changes = 0;
    const replacements = [
        [new RegExp('\u00e2\u20ac\u201d', 'g'), '-'],
        [new RegExp('\u00e2\u20ac\u201c', 'g'), '-'],
        [new RegExp('\u00e2\u20ac\u00a2', 'g'), '|'],
        [new RegExp('\u00c3\u2014', 'g'), 'x'],
        [new RegExp('\u00f0\u0178\u201d\u201e', 'g'), 'Recurring'],
        [new RegExp('\u00f0\u0178\u2019\u00b3', 'g'), 'Card']
    ];
    Object.keys(value).forEach(key => {
        if (typeof value[key] === 'string') {
            let cleaned = value[key];
            replacements.forEach(([pattern, replacement]) => { cleaned = cleaned.replace(pattern, replacement); });
            if (cleaned !== value[key]) { value[key] = cleaned; changes += 1; }
        } else if (value[key] && typeof value[key] === 'object') changes += sanitizeStoredEncoding(value[key], seen);
    });
    return changes;
}
function migrateDatabase() {
    const encodingFixes = sanitizeStoredEncoding(state);

    let migrated = encodingFixes > 0;
    
    // Legacy migration (month keys -> year-month keys)
    if (state.personalCalendar && Object.keys(state.personalCalendar).length > 0) {
        const firstKey = Object.keys(state.personalCalendar)[0];
        if (!firstKey.includes('-')) {
            const migratedPersonal = {};
            const migratedBills = {};
            
            for (const [month, txList] of Object.entries(state.personalCalendar)) {
                migratedPersonal[`2027-${month}`] = txList;
            }
            state.personalCalendar = migratedPersonal;
            
            for (const [month, billData] of Object.entries(state.monthlyBills)) {
                migratedBills[`2027-${month}`] = billData;
            }
            state.monthlyBills = migratedBills;
            
            migrated = true;
        }
    }
    
    // Joint Register dates assignment
    if (state.jointRegister && state.jointRegister.length > 0 && !state.jointRegister[0].date) {
        state.jointRegister = assignDatesToJointRegister(state.jointRegister);
        migrated = true;
    }
    
    // Ensure all perpetual state variables exist
    if (state.currentYear === undefined) { state.currentYear = 2026; migrated = true; }
    if (state.currentMonth === undefined) { state.currentMonth = 'Jul'; migrated = true; }
    if (state.dashboardType === undefined) { state.dashboardType = 'personal'; migrated = true; }
    if (state.viewMode === undefined) { state.viewMode = 'calendar'; migrated = true; }
    if (state.listScope === undefined) { state.listScope = 'month'; migrated = true; }
    if (!Number.isFinite(Number(state.savingsCurrentAmount))) { state.savingsCurrentAmount = 0; migrated = true; }
    if (!Number.isFinite(Number(state.savingsStartingBalance))) { state.savingsStartingBalance = Number(state.savingsCurrentAmount) || 0; migrated = true; }
    if (!Array.isArray(state.savingsTransactions)) { state.savingsTransactions = []; migrated = true; }
    if (!['calendar', 'list'].includes(state.savingsViewMode)) { state.savingsViewMode = 'calendar'; migrated = true; }
    if (!['month', 'year'].includes(state.savingsListScope)) { state.savingsListScope = 'month'; migrated = true; }
    if (state.savingsMetricsCollapsed === undefined) { state.savingsMetricsCollapsed = false; migrated = true; }
    if (state.savingsYearSummaryCollapsed === undefined) { state.savingsYearSummaryCollapsed = false; migrated = true; }
    if (!state.recurringChargeTemplates) { state.recurringChargeTemplates = {}; migrated = true; }
    if (!state.allocationTemplates) { state.allocationTemplates = {}; migrated = true; }
    if (!state.allocationRecurrenceSkips) { state.allocationRecurrenceSkips = {}; migrated = true; }
    if (!state.allocationRecurrenceStops) { state.allocationRecurrenceStops = {}; migrated = true; }
    if (!state.allocationOffsetNamesCleaned) {
        Object.values(state.monthlyBills || {}).forEach(monthData => {
            ['cycle1st', 'cycle15th'].forEach(cycleKey => {
                (monthData?.[cycleKey]?.contributions || []).forEach(allocation => {
                    if ((allocation.role || 'base') === 'offset' && typeof allocation.name === 'string') {
                        allocation.name = allocation.name.replace(/ \(Offset\)$/, '');
                    }
                });
            });
        });
        state.allocationOffsetNamesCleaned = true;
        migrated = true;
    }
    if (!state.allocationsPolarityFlipped20260715) {
        Object.values(state.monthlyBills || {}).forEach(monthData => {
            ['cycle1st', 'cycle15th'].forEach(cycleKey => {
                if (!monthData?.[cycleKey]) return;
                (monthData[cycleKey].contributions || []).forEach(allocation => {
                    if (allocation.jason !== null && allocation.jason !== undefined) {
                        allocation.jason = -allocation.jason;
                    }
                    if (allocation.asia !== null && allocation.asia !== undefined) {
                        allocation.asia = -allocation.asia;
                    }
                    if (allocation.sourceJason !== null && allocation.sourceJason !== undefined) {
                        allocation.sourceJason = -allocation.sourceJason;
                    }
                    if (allocation.sourceAsia !== null && allocation.sourceAsia !== undefined) {
                        allocation.sourceAsia = -allocation.sourceAsia;
                    }
                });
            });
        });
        Object.values(state.allocationTemplates || {}).forEach(template => {
            if (template.jason !== null && template.jason !== undefined) {
                template.jason = -template.jason;
            }
            if (template.asia !== null && template.asia !== undefined) {
                template.asia = -template.asia;
            }
            if (template.offsetJason !== null && template.offsetJason !== undefined) {
                template.offsetJason = -template.offsetJason;
            }
            if (template.offsetAsia !== null && template.offsetAsia !== undefined) {
                template.offsetAsia = -template.offsetAsia;
            }
        });
        state.allocationsPolarityFlipped20260715 = true;
        migrated = true;
    }
    if (!state.seasonalExpenses) { state.seasonalExpenses = []; migrated = true; }
    if (!state.manualTransfers) { state.manualTransfers = []; migrated = true; }
    if (!state.deliveryBudgets) { state.deliveryBudgets = {}; migrated = true; }
    if (!state.billsAndAllocationsCleared20260714) {
        Object.values(state.monthlyBills || {}).forEach(monthData => {
            ['cycle1st', 'cycle15th'].forEach(cycleKey => {
                if (!monthData?.[cycleKey]) return;
                monthData[cycleKey].bills = [];
                monthData[cycleKey].contributions = [];
                monthData[cycleKey].totals = { jason: 0, asia: 0, billsTotal: 0 };
            });
        });
        Object.keys(state.personalCalendar || {}).forEach(key => {
            state.personalCalendar[key] = (state.personalCalendar[key] || []).filter(tx => !tx.splitterItem && !tx.linkedBillId && !tx.seasonalExpenseId);
        });
        state.jointRegister = (state.jointRegister || []).filter(tx => !tx.splitterItem && !tx.linkedBillId && !tx.seasonalExpenseId);
        Object.values(state.cardCalendars || {}).forEach(calendar => {
            Object.keys(calendar || {}).forEach(key => {
                calendar[key] = (calendar[key] || []).filter(tx => !tx.splitterItem && !tx.linkedBillId && !tx.seasonalExpenseId);
            });
        });
        state.billRecurrenceTemplates = {};
        state.billRecurrenceSkips = {};
        state.billRecurrenceStops = {};
        state.billLegacyRecurrenceStops = {};
        state.allocationTemplates = {};
        state.allocationRecurrenceSkips = {};
        state.allocationRecurrenceStops = {};
        state.seasonalExpenses = [];
        state.billsAndAllocationsCleared20260714 = true;
        migrated = true;
    }
    // Remove legacy manually seeded personal-calendar entries; preserve recurring and dynamic transactions.
    if (!state.personalStaticTransactionsCleared20260715) {
        Object.keys(state.personalCalendar || {}).forEach(key => {
            state.personalCalendar[key] = (state.personalCalendar[key] || []).filter(tx =>
                tx.isRecurring === true || tx.isRecurringOccurrence === true ||
                tx.isSplitterDynamic === true || isDynamicTxId(tx.id)
            );
        });
        state.personalStaticTransactionsCleared20260715 = true;
        migrated = true;
    }
    if (state.loansFilter === undefined) { state.loansFilter = 'credit'; migrated = true; }
    
    // Credit card sub-dashboard states
    if (state.ccSelectedCardId === undefined) { state.ccSelectedCardId = ''; migrated = true; }
    if (state.ccViewMode === undefined) { state.ccViewMode = 'calendar'; migrated = true; }
    if (state.ccListScope === undefined) { state.ccListScope = 'month'; migrated = true; }
    if (state.ccYear === undefined) { state.ccYear = 2026; migrated = true; }
    if (state.ccMonth === undefined) { state.ccMonth = 'Jul'; migrated = true; }
    if (state.ccSelectedDate === undefined) { state.ccSelectedDate = '2026-07-14'; migrated = true; }
    
    if (state.payrollConfig === undefined) {
        state.payrollConfig = {
            firstPayDate: '2026-01-02',
            baseNetPay: 2900,
            stipendAmount: 150,
            hasDifferentRates: false,
            differentRates: {
                rate1st: 3050,
                rate2nd: 2900,
                rate3rd: 2900
            },
            estimates: [],
            skippedPaychecks: []
        };
        migrated = true;
    }
    if (state.payrollConfig.skippedPaychecks === undefined) {
        state.payrollConfig.skippedPaychecks = [];
        migrated = true;
    }
    if (state.skippedTransfers === undefined) {
        state.skippedTransfers = [];
        migrated = true;
    }
    if (state.listSort === undefined) {
        state.listSort = { key: 'date', direction: 'asc' };
        migrated = true;
    }
    if (state.listCycleFilter === undefined) {
        state.listCycleFilter = 'all';
        migrated = true;
    }
    if (!['joint', 'personal'].includes(state.billTrackerOwnership)) {
        state.billTrackerOwnership = 'joint';
        migrated = true;
    }
    if (!state.billTrackerSorts) {
        state.billTrackerSorts = { joint: { key: 'account', direction: 'asc' }, personal: { key: 'dueDay', direction: 'asc' }, allocations: { key: 'name', direction: 'asc' } };
        migrated = true;
    }
    if (!['month', '1st', '15th'].includes(state.billMetricsCycle)) {
        state.billMetricsCycle = 'month';
        migrated = true;
    }
    if (!state.orphanedPersonalRecurringBillsRestored20260715v3) {
        const restoredCount = restoreOrphanedPersonalRecurringBills();
        state.orphanedPersonalRecurringBillsRestored20260715v3 = true;
        if (restoredCount > 0) migrated = true;
    }
    
    if (!state.billTrackerSettings) {
        state.billTrackerSettings = [];
        migrated = true;
    }

    
    // Ensure loans array is self-healed
    if (state.loans) {
        // Seed discover_card if not exists
        if (!state.loans.some(l => l.id === 'discover_card')) {
            state.loans.unshift({ id: 'discover_card', name: 'Discover Card', startBal: 5000, currentBal: 2450, monthlyMin: 75, type: 'credit', interestRate: 22.9, dueDay: 10, promos: [] });
            migrated = true;
        }
        
        state.loans.forEach(loan => {
            if (loan.type === undefined) {
                loan.type = (loan.id === 'discover_card' ? 'credit' : 'loan');
                migrated = true;
            }
            if (loan.interestRate === undefined) {
                loan.interestRate = (loan.id === 'discover_card' ? 22.9 : (loan.id === 'upstart' ? 7.9 : (loan.id === 'bathroom' ? 5.9 : (loan.id === 'lightstream' ? 6.5 : (loan.id === 'federal_loans' ? 4.5 : (loan.id === 'texas_loans' ? 5.0 : 0))))));
                migrated = true;
            }
            if (loan.dueDay === undefined) {
                loan.dueDay = (loan.id === 'discover_card' ? 10 : (loan.id === 'greensky' ? 5 : (loan.id === 'bathroom' ? 20 : (loan.id === 'lightstream' ? 18 : (loan.id === 'federal_loans' ? 25 : (loan.id === 'texas_loans' ? 22 : 15))))));
                migrated = true;
            }
            if (loan.promos === undefined) {
                loan.promos = [];
                migrated = true;
            }
            if (loan.limit === undefined) {
                loan.limit = loan.startBal || 5000;
                migrated = true;
            }
            if (loan.isChargeCard === undefined) {
                loan.isChargeCard = false;
                migrated = true;
            }
            if (loan.promoActive === undefined) {
                loan.promoActive = false;
                migrated = true;
            }
            if (loan.promoRate === undefined) {
                loan.promoRate = 0;
                migrated = true;
            }
            if (loan.promoExpDate === undefined) {
                loan.promoExpDate = '';
                migrated = true;
            }
        });
    }
    
    // Ensure all transactions have unique IDs
    let idAssigned = false;
    if (state.personalCalendar) {
        for (const [key, txList] of Object.entries(state.personalCalendar)) {
            txList.forEach(tx => {
                if (!tx.id) {
                    tx.id = 'p-' + Math.random().toString(36).substr(2, 9);
                    idAssigned = true;
                }
            });
        }
    }
    if (state.jointRegister) {
        state.jointRegister.forEach(tx => {
            if (!tx.id) {
                tx.id = 'j-' + Math.random().toString(36).substr(2, 9);
                idAssigned = true;
            }
        });
    }
    if (idAssigned) {
        migrated = true;
    }
    
    if (state.cardCalendars === undefined) {
        state.cardCalendars = {};
        migrated = true;
    }
    
    // Add defaults to monthly bills templates if missing
    if (state.monthlyBills) {
        for (const [key, billData] of Object.entries(state.monthlyBills)) {
            ['cycle1st', 'cycle15th'].forEach(cKey => {
                const defaultDay = cKey === 'cycle1st' ? 1 : 15;
                if (billData[cKey] && billData[cKey].bills) {
                    billData[cKey].bills.forEach(bill => {
                        if (bill.dueDay === undefined) {
                            bill.dueDay = defaultDay;
                            migrated = true;
                        }
                        if (bill.paymentSource === undefined) {
                            bill.paymentSource = 'jointChecking';
                            migrated = true;
                        }
                    });
                }
            });
        }
    }
    
    // Ensure dynamicOverrides exists (for editing/deleting dynamic splitter transactions)
    if (!state.dynamicOverrides) { state.dynamicOverrides = {}; migrated = true; }

    // Delivery Earnings Enhancements migration
    if (state.deliveryYearSummaryCollapsed === undefined) {
        state.deliveryYearSummaryCollapsed = false;
        migrated = true;
    }
    if (state.deliveryEarnings) {
        let cleanedGigs = false;
        state.deliveryEarnings.forEach(rec => {
            if (rec.instacart !== undefined && rec.instacart !== 0) {
                rec.instacart = 0;
                cleanedGigs = true;
            }
            const calculatedTotal = (rec.cash || 0) + (rec.sideGigs || 0) + (rec.grubHub || 0) + (rec.uberEats || 0);
            if (rec.total !== calculatedTotal) {
                rec.total = calculatedTotal;
                cleanedGigs = true;
            }
        });
        if (cleanedGigs) migrated = true;
    }

    if (migrated) {
        saveDatabase();
        console.log("Database migrated to perpetual structure.");
    }
}

// Helper: check if a transaction ID belongs to a dynamic splitter transaction
function isDynamicTxId(id) {
    if (!id) return false;
    const s = String(id);
    return s.startsWith('xfer-1st-') || s.startsWith('xfer-15th-') ||
           s.startsWith('joint-xfer-jason-') || s.startsWith('joint-xfer-asia-') ||
           s.startsWith('dynamic-paycheck-') || s.startsWith('dynamic-delivery-');
}

// Jason's dynamic joint contribution and personal transfer represent the same money movement.
function getLinkedDynamicTxId(id) {
    const value = String(id || '');
    let match = value.match(/^xfer-(1st|15th)-(\d{4})-([A-Z][a-z]{2})$/);
    if (match) return `joint-xfer-jason-${match[1]}-${match[2]}-${match[3]}`;

    match = value.match(/^joint-xfer-jason-(1st|15th)-(\d{4})-([A-Z][a-z]{2})$/);
    if (match) return `xfer-${match[1]}-${match[2]}-${match[3]}`;
    return null;
}

function saveDynamicTxOverride(id, override) {
    if (!state.dynamicOverrides) state.dynamicOverrides = {};
    state.dynamicOverrides[id] = { ...(state.dynamicOverrides[id] || {}), ...override };

    const linkedId = getLinkedDynamicTxId(id);
    if (!linkedId) return;

    const linkedOverride = { ...override };
    if (linkedOverride.amount !== undefined) {
        linkedOverride.amount = linkedId.startsWith('xfer-')
            ? -Math.abs(linkedOverride.amount)
            : Math.abs(linkedOverride.amount);
    }
    state.dynamicOverrides[linkedId] = {
        ...(state.dynamicOverrides[linkedId] || {}),
        ...linkedOverride
    };
}

function navigateToDeliveryWeek(targetDateStr) {
    const parts = targetDateStr.split('-');
    if (parts.length !== 3) return;
    const yr = parseInt(parts[0]);
    const monthIndex = parseInt(parts[1]) - 1;
    const mShort = MONTH_ORDER[monthIndex];
    
    state.currentYear = yr;
    state.currentMonth = mShort;
    
    const monthSelect = document.getElementById('month-select');
    const yearSelect = document.getElementById('year-select');
    if (monthSelect) monthSelect.value = state.currentMonth;
    if (yearSelect) yearSelect.value = state.currentYear;
    
    state.ccYear = state.currentYear;
    state.ccMonth = state.currentMonth;
    
    const weeks = getDeliveryWeeksForMonth(state.currentMonth);
    const activeWeekIdx = weeks.findIndex(w => w.some(d => d.date === targetDateStr));
    if (activeWeekIdx !== -1) {
        state.deliveryWeekIndex = activeWeekIdx;
    } else {
        state.deliveryWeekIndex = 0;
    }
    
    updateTabTitles();
    switchToTab('delivery');
    renderApp();
}

// Open a lightweight edit/delete dialog for dynamic transactions
function openDynamicTxEditor(txId, txDate, currentDesc, currentAmount) {
    if (!state.dynamicOverrides) state.dynamicOverrides = {};
    const existing = state.dynamicOverrides[txId] || {};
    const desc = existing.description || currentDesc;
    const amt = (existing.amount !== undefined) ? existing.amount : currentAmount;

    const dialog = document.getElementById('edit-tx-dialog');
    document.getElementById('edit-tx-id').value = txId;
    document.getElementById('edit-tx-date-orig').value = txDate;
    document.getElementById('edit-tx-date').value = txDate;
    document.getElementById('edit-tx-mode').value = 'dynamic-override';
    document.getElementById('edit-tx-modal-title').textContent = 'Edit / Delete Dynamic Transaction';
    document.getElementById('btn-save-edit-tx').textContent = 'Save Override';
    document.getElementById('btn-duplicate-edit-tx').classList.add('hidden');
    document.getElementById('edit-tx-desc').value = desc;
    document.getElementById('edit-tx-amount').value = Math.abs(amt);
    // Show amount group, hide contrib group
    document.getElementById('edit-joint-contrib-group').classList.add('hidden');
    document.getElementById('edit-amount-group').classList.remove('hidden');
    document.getElementById('edit-merchant-group').classList.add('hidden');
    document.getElementById('edit-card-meta-group').classList.add('hidden');
    document.getElementById('edit-recurring-group').classList.add('hidden');
    document.getElementById('edit-payment-plan-group').classList.add('hidden');
    
    const goDeliveryBtn = document.getElementById('btn-go-to-delivery-log');
    if (goDeliveryBtn) {
        if (txId && txId.startsWith('dynamic-delivery-')) {
            goDeliveryBtn.classList.remove('hidden');
            goDeliveryBtn.onclick = () => {
                dialog.close();
                navigateToDeliveryWeek(txDate);
            };
        } else {
            goDeliveryBtn.classList.add('hidden');
            goDeliveryBtn.onclick = null;
        }
    }
    
    dialog.showModal();
}

function resetToDefaults() {
    if (window.INITIAL_BUDGET_DATA) {
        state.deliveryEarnings = JSON.parse(JSON.stringify(window.INITIAL_BUDGET_DATA.deliveryEarnings));
        state.taxSavings = JSON.parse(JSON.stringify(window.INITIAL_BUDGET_DATA.taxSavings));
        state.jointRegister = JSON.parse(JSON.stringify(window.INITIAL_BUDGET_DATA.jointRegister));
        state.loans = JSON.parse(JSON.stringify(DEFAULT_LOANS));
        
        // Seed 2027 monthly templates
        state.personalCalendar = {};
        state.monthlyBills = {};
        state.cardCalendars = {};
        for (const [month, txList] of Object.entries(window.INITIAL_BUDGET_DATA.personalCalendar)) {
            state.personalCalendar[`2027-${month}`] = txList;
        }
        for (const [month, billData] of Object.entries(window.INITIAL_BUDGET_DATA.monthlyBills)) {
            state.monthlyBills[`2027-${month}`] = billData;
        }
        
        // Convert joint register preloads
        state.jointRegister = assignDatesToJointRegister(state.jointRegister);
        
        // Setup initial default active period (July 2026)
        state.currentYear = 2026;
        state.currentMonth = 'Jul';
        state.dashboardType = 'personal';
        state.viewMode = 'calendar';
        state.listScope = 'month';
        state.savingsCurrentAmount = 0;
        state.savingsStartingBalance = 0;
        state.savingsTransactions = [];
        state.savingsViewMode = 'calendar';
        state.savingsListScope = 'month';
        state.savingsMetricsCollapsed = false;
        state.savingsYearSummaryCollapsed = false;
        state.deliveryWeekIndex = 0;

        // Mark the one-time cleanup migrations in migrateDatabase() as already satisfied. Without
        // this, reloading the page after a reset would run those migrations against the freshly
        // seeded data on the next load and immediately wipe the bills/allocations/personal-calendar
        // entries this function just restored (and double-flip allocation sign polarity).
        state.allocationOffsetNamesCleaned = true;
        state.allocationsPolarityFlipped20260715 = true;
        state.billsAndAllocationsCleared20260714 = true;
        state.personalStaticTransactionsCleared20260715 = true;

        saveDatabase();
        logSystem("Database reset to original spreadsheet data (perpetual structure initialized).");
    } else {
        console.error("INITIAL_BUDGET_DATA not loaded in global window context.");
    }
}

// Lazy loader for new year-months
function ensureYearMonthInitialized(year, month) {
    const key = `${year}-${month}`;
    if (!state.personalCalendar[key]) {
        const templatePersonal = window.INITIAL_BUDGET_DATA.personalCalendar[month] || [];
        state.personalCalendar[key] = templatePersonal.filter(tx =>
            tx.isRecurring === true || tx.isRecurringOccurrence === true ||
            tx.isSplitterDynamic === true || isDynamicTxId(tx.id)
        ).map(tx => {
            const dateParts = tx.date.split('-');
            const newDate = `${year}-${dateParts[1]}-${dateParts[2]}`;
            return { ...tx, date: newDate };
        });
    }
    
    if (!state.monthlyBills[key]) {
        const emptyBills = {
            cycle1st: { label: `1st of ${month}`, bills: [], contributions: [], totals: { jason: 0, asia: 0, billsTotal: 0 } },
            cycle15th: { label: `15th of ${month}`, bills: [], contributions: [], totals: { jason: 0, asia: 0, billsTotal: 0 } }
        };
        const templateBills = state.billsAndAllocationsCleared20260714
            ? emptyBills
            : (window.INITIAL_BUDGET_DATA.monthlyBills[month] || emptyBills);
        state.monthlyBills[key] = JSON.parse(JSON.stringify(templateBills));
        autopopulateBillsForMonth(year, month);
    }
}

function formatLocalDate(date) {
    return `${date.getFullYear()}-${String(date.getMonth() + 1).padStart(2, '0')}-${String(date.getDate()).padStart(2, '0')}`;
}

// Formats a card/loan balance, labeling a negative balance (e.g. from an overpayment) as a credit
// instead of showing a bare "$-50.00", which reads as a formatting error rather than money owed back.
function formatCardBalance(balance) {
    const val = Number(balance) || 0;
    return val < 0 ? `$${Math.abs(val).toFixed(2)} credit` : `$${val.toFixed(2)}`;
}

// Jumps to a specific card's or loan's dashboard, focused on the month/day of the given payment
// date. Routes to the Credit Cards tab or the Loans tab depending on the target's type. Used by the
// "View in Credit Cards"/"View in Loans" links on synchronized splitter rows and ledger entries so
// the user can manage the payment at its source.
function goToCardPaymentInCreditCards(cardId, dateStr) {
    const card = state.loans.find(l => l.id === cardId);
    if (!card) { alert('The linked credit card or loan could not be found.'); return; }
    ['edit-tx-dialog', 'joint-bill-dialog'].forEach(id => {
        const d = document.getElementById(id);
        if (d && d.open) d.close();
    });
    state.ccSelectedCardId = cardId;
    state.ccViewMode = 'calendar';
    if (dateStr) {
        const dObj = new Date(dateStr + 'T00:00:00');
        if (!Number.isNaN(dObj.getTime())) {
            state.ccYear = dObj.getFullYear();
            state.ccMonth = MONTH_ORDER[dObj.getMonth()];
            state.ccSelectedDate = dateStr;
        }
    }
    switchToTab(card.type === 'loan' ? 'loans' : 'creditcards');
    saveDatabase();
    renderApp();
}

// After deleting a checking-side card payment, removes its card-side leg (matched by
// linkedPaymentId) and restores the card's balance. The Bill Splitter row for the payment is
// swept automatically on the next sync once the backing payment is gone.
function removeLinkedCardPaymentLeg(removedTx) {
    if (!removedTx || !removedTx.linkedPaymentId) return;
    Object.keys(state.cardCalendars || {}).forEach(cId => {
        Object.values(state.cardCalendars[cId] || {}).forEach(list => {
            const idx = (list || []).findIndex(t => t.linkedPaymentId === removedTx.linkedPaymentId);
            if (idx > -1) {
                const cardLeg = list.splice(idx, 1)[0];
                const cardObj = state.loans.find(l => l.id === cId);
                if (cardObj) cardObj.currentBal = Math.max(0, (Number(cardObj.currentBal) || 0) + Math.abs(Number(cardLeg.amount) || 0));
            }
        });
    });
}

// Mirror of removeLinkedCardPaymentLeg for the opposite direction: after deleting a card/loan-side
// payment leg, removes the matching checking-side transaction (personal or joint) so a payment
// deleted from a card's own ledger also disappears from the Proposed Future Payments table and the
// Bill Splitter (which is swept automatically once the backing checking-side tx is gone).
function removeLinkedCheckingPaymentLeg(removedCardTx) {
    if (!removedCardTx || !removedCardTx.linkedPaymentId) return;
    Object.values(state.personalCalendar || {}).forEach(list => {
        const idx = (list || []).findIndex(t => t.linkedPaymentId === removedCardTx.linkedPaymentId);
        if (idx > -1) list.splice(idx, 1);
    });
    if (state.jointRegister) {
        const idx = state.jointRegister.findIndex(t => t.linkedPaymentId === removedCardTx.linkedPaymentId);
        if (idx > -1) state.jointRegister.splice(idx, 1);
    }
}

// Finds the card-side leg of an automatic payment by its automaticPaymentId.
function findAutomaticCardLeg(automaticPaymentId) {
    if (!automaticPaymentId) return null;
    for (const calendar of Object.values(state.cardCalendars || {})) {
        for (const list of Object.values(calendar || {})) {
            const match = (list || []).find(tx => tx.automaticPaymentId === automaticPaymentId && tx.isAutomaticCardPayment);
            if (match) return match;
        }
    }
    return null;
}

function parseFormula(value) {
    if (typeof value !== 'string') return Number(value) || 0;
    const trimmed = value.trim();
    if (!trimmed) return 0;
    if (trimmed.startsWith('=')) {
        const expr = trimmed.slice(1).replace(/\s+/g, '');
        // Validate expression contains only numbers, decimal points, and + - * / ( )
        const safeRegex = /^[0-9+\-*/().]+$/;
        if (safeRegex.test(expr)) {
            try {
                // Safely evaluate math expression
                const result = Function(`"use strict"; return (${expr})`)();
                return Number(result) || 0;
            } catch (err) {
                console.error("Formula parsing error:", err);
                return 0;
            }
        } else {
            alert("Invalid formula. Only numbers and basic operators (+, -, *, /) are allowed.");
            return 0;
        }
    }
    return parseFloat(trimmed) || 0;
}

function isMobileViewport() {
    return window.matchMedia('(max-width: 900px)').matches;
}

function closeMobileSidebar() {
    const sidebar = document.querySelector('.app-sidebar');
    const backdrop = document.getElementById('sidebar-backdrop');
    if (sidebar) sidebar.classList.remove('mobile-open');
    if (backdrop) backdrop.classList.remove('visible');
}

function openGigEntryDialog(date, key, label) {
    const dialog = document.getElementById('gig-entry-dialog');
    const input = document.getElementById('gig-entry-input');
    const subtitle = document.getElementById('gig-entry-subtitle');
    if (!dialog || !input) return;

    const rec = state.deliveryEarnings.find(item => item.date === date);
    const currentVal = rec ? (rec[key + 'Formula'] || (rec[key] ? String(rec[key]) : '')) : '';

    dialog.dataset.date = date;
    dialog.dataset.key = key;
    subtitle.textContent = `${label} — ${date}`;
    input.value = currentVal;

    dialog.showModal();
    setTimeout(() => { input.focus(); input.select(); }, 50);
}

// Date -> record index for state.deliveryEarnings, used only by the hot ensureDeliveryEarningForDate
// path below (called ~30-40x per month while simulating the balance-adjusted calendar transfers).
// Everywhere else in the file still reads/writes the array directly with .find()/.push()/.filter(),
// so instead of keeping this index incrementally in sync with every one of those call sites, it just
// self-heals: any time the array's length no longer matches what the index was built from, it's rebuilt.
let _deliveryEarningsIndex = null;
let _deliveryEarningsIndexLength = -1;

function getDeliveryEarningsIndex() {
    if (!_deliveryEarningsIndex || _deliveryEarningsIndexLength !== state.deliveryEarnings.length) {
        _deliveryEarningsIndex = new Map();
        state.deliveryEarnings.forEach(rec => _deliveryEarningsIndex.set(rec.date, rec));
        _deliveryEarningsIndexLength = state.deliveryEarnings.length;
    }
    return _deliveryEarningsIndex;
}

function ensureDeliveryEarningForDate(date) {
    const dateStr = formatLocalDate(date);
    const index = getDeliveryEarningsIndex();
    let record = index.get(dateStr);
    if (!record) {
        const dayNames = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
        record = { date: dateStr, day: dayNames[date.getDay()], cash: 0, sideGigs: 0, grubHub: 0, uberEats: 0, total: 0, noEarnCash: false, noEarnSideGigs: false, noEarnGrubHub: false, noEarnUberEats: false, offDayReason: '' };
        state.deliveryEarnings.push(record);
        index.set(dateStr, record);
        _deliveryEarningsIndexLength = state.deliveryEarnings.length;
    }
    return record;
}

// Dynamically generate daily earnings records for delivery gig logs
function ensureDeliveryEarningsForMonth(year, month) {
    const monthIndex = MONTH_ORDER.indexOf(month);
    if (monthIndex === -1) return;
    
    const numDays = new Date(year, monthIndex + 1, 0).getDate();
    const dayNames = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
    
    let updated = false;
    for (let d = 1; d <= numDays; d++) {
        const dateStr = `${year}-${String(monthIndex + 1).padStart(2, '0')}-${String(d).padStart(2, '0')}`;
        const exists = state.deliveryEarnings.some(g => g.date === dateStr);
        if (!exists) {
            const dateObj = new Date(year, monthIndex, d);
            const dayName = dayNames[dateObj.getDay()];
            state.deliveryEarnings.push({
                date: dateStr,
                day: dayName,
                cash: 0,
                sideGigs: 0,
                grubHub: 0,
                uberEats: 0,
                total: 0,
                noEarnCash: false,
                noEarnSideGigs: false,
                noEarnGrubHub: false,
                noEarnUberEats: false,
                offDayReason: ''
            });
            updated = true;
        }
    }
    
    if (updated) {
        state.deliveryEarnings.sort((a, b) => new Date(a.date).getTime() - new Date(b.date).getTime());
        saveDatabase();
    }
}

function updateSegmentedControlsUI() {
    // 1. Dashboard Type
    document.querySelectorAll('#dashboard-toggle-container .segment-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.type === state.dashboardType);
    });
    
    // 2. View Mode
    document.querySelectorAll('#view-toggle-container .segment-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.mode === state.viewMode);
    });
    
    // 3. List Scope (only visible if viewMode === 'list')
    const scopeContainer = document.getElementById('scope-toggle-container');
    if (state.viewMode === 'list') {
        scopeContainer.classList.remove('hidden');
        document.querySelectorAll('#scope-toggle-container .segment-btn').forEach(btn => {
            btn.classList.toggle('active', btn.dataset.scope === state.listScope);
        });
    } else {
        scopeContainer.classList.add('hidden');
    }
    
    // 4. Loans category filter toggle
    document.querySelectorAll('#loans-type-filter-container .segment-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.filter === (state.loansFilter || 'credit'));
    });
}


function switchToTab(tabName) {
    const btn = document.querySelector(`.nav-btn[data-tab="${tabName}"]`);
    if (btn) {
        document.querySelectorAll('.nav-btn').forEach(b => b.classList.remove('active'));
        document.querySelectorAll('.tab-view').forEach(v => v.classList.remove('active'));
        
        btn.classList.add('active');
        const view = document.getElementById(`view-${tabName}`);
        if (view) view.classList.add('active');
        
        if (tabName !== 'creditcards') {
            state.ccSelectedCardId = '';
        }
        
        // Toggle visibility of top sub-toggles depending on Dashboard active tab
        const controls = document.querySelector('.header-controls');
        if (controls) {
            if (tabName === 'dashboard') {
                document.getElementById('dashboard-toggle-container').classList.remove('hidden');
                document.getElementById('view-toggle-container').classList.remove('hidden');
                if (state.viewMode === 'list') {
                    document.getElementById('scope-toggle-container').classList.remove('hidden');
                    document.getElementById('cycle-filter-container').classList.remove('hidden');
                } else {
                    document.getElementById('scope-toggle-container').classList.add('hidden');
                    document.getElementById('cycle-filter-container').classList.add('hidden');
                }
                const toggle = document.getElementById('bills-metrics-cycle-toggle');
                if (toggle) toggle.classList.add('hidden');
            } else if (tabName === 'bills') {
                document.getElementById('dashboard-toggle-container').classList.add('hidden');
                document.getElementById('view-toggle-container').classList.add('hidden');
                document.getElementById('scope-toggle-container').classList.add('hidden');
                document.getElementById('cycle-filter-container').classList.add('hidden');
                const toggle = document.getElementById('bills-metrics-cycle-toggle');
                if (toggle) toggle.classList.remove('hidden');
            } else {
                document.getElementById('dashboard-toggle-container').classList.add('hidden');
                document.getElementById('view-toggle-container').classList.add('hidden');
                document.getElementById('scope-toggle-container').classList.add('hidden');
                document.getElementById('cycle-filter-container').classList.add('hidden');
                const toggle = document.getElementById('bills-metrics-cycle-toggle');
                if (toggle) toggle.classList.add('hidden');
            }
        }
        
        // Automatically collapse maximized calendar view when switching tabs
        if (document.body.classList.contains('maximized-calendar')) {
            document.body.classList.remove('maximized-calendar');
            document.querySelectorAll('#btn-toggle-layout-maximize').forEach(btn => {
                btn.textContent = '⤢ Expand View';
                btn.title = 'Toggle full-screen calendar';
            });
        }

        if (tabName === 'delivery') {
            const today = new Date();
            const todayStr = formatLocalDate(today);
            const weeks = getDeliveryWeeksForMonth(state.currentMonth);
            const wIdx = weeks.findIndex(w => w.some(g => g.date === todayStr));
            if (wIdx >= 0) {
                state.deliveryWeekIndex = wIdx;
            }
        }

        updateTabTitles();
        renderApp();
    }
}

// --- EVENT LISTENERS ---
function setupEventListeners() {
    setupBillTrackerListeners();
    document.getElementById('btn-close-day-highlights').addEventListener('click', () => {
        document.getElementById('day-highlights-dialog').close();
    });

    // Tab switching
    document.querySelectorAll('.nav-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            const btnTarget = e.currentTarget;
            const tab = btnTarget.dataset.tab;
            switchToTab(tab);
            closeMobileSidebar();
        });
    });

    // Mobile sidebar toggle
    const mobileSidebar = document.querySelector('.app-sidebar');
    const mobileToggleBtn = document.getElementById('btn-mobile-nav-toggle');
    const mobileCloseBtn = document.getElementById('btn-mobile-nav-close');
    const mobileBackdrop = document.getElementById('sidebar-backdrop');
    if (mobileToggleBtn) {
        mobileToggleBtn.addEventListener('click', () => {
            mobileSidebar.classList.add('mobile-open');
            mobileBackdrop.classList.add('visible');
        });
    }
    if (mobileCloseBtn) {
        mobileCloseBtn.addEventListener('click', closeMobileSidebar);
    }
    if (mobileBackdrop) {
        mobileBackdrop.addEventListener('click', closeMobileSidebar);
    }

    // Re-render delivery grid if crossing the mobile breakpoint (readonly attr depends on it)
    let _lastIsMobile = isMobileViewport();
    window.addEventListener('resize', () => {
        const nowMobile = isMobileViewport();
        if (nowMobile !== _lastIsMobile) {
            _lastIsMobile = nowMobile;
            renderApp();
        }
        if (!nowMobile) closeMobileSidebar();
    });

    // Mobile gig earnings entry dialog
    const gigEntryDialog = document.getElementById('gig-entry-dialog');
    const gigEntryInput = document.getElementById('gig-entry-input');
    const gigEntryForm = document.getElementById('gig-entry-form');
    const gigEntryCancelBtn = document.getElementById('btn-cancel-gig-entry');
    if (gigEntryInput) {
        gigEntryInput.addEventListener('input', (e) => {
            const filtered = e.target.value.replace(/[^0-9+\-*/.=() ]/g, '');
            if (filtered !== e.target.value) {
                e.target.value = filtered;
            }
        });
        gigEntryInput.addEventListener('keydown', (e) => {
            if (e.key === 'Enter') {
                e.preventDefault();
                gigEntryForm.requestSubmit();
            }
        });
    }
    if (gigEntryCancelBtn) {
        gigEntryCancelBtn.addEventListener('click', () => gigEntryDialog.close());
    }
    if (gigEntryForm) {
        gigEntryForm.addEventListener('submit', (e) => {
            e.preventDefault();
            const date = gigEntryDialog.dataset.date;
            const key = gigEntryDialog.dataset.key;
            const rawVal = gigEntryInput.value.trim();
            const parsedVal = parseFormula(rawVal);

            const rec = state.deliveryEarnings.find(item => item.date === date);
            if (rec) {
                rec[key + 'Formula'] = rawVal;
                rec[key] = parsedVal;
                rec.total = (rec.cash || 0) + (rec.sideGigs || 0) + (rec.grubHub || 0) + (rec.uberEats || 0);
                saveDatabase();
                renderApp();
            }
            gigEntryDialog.close();
        });
    }

    // Segmented Dashboard toggles (Personal vs Joint)
    document.querySelectorAll('#dashboard-toggle-container .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            state.dashboardType = e.target.dataset.type;
            updateSegmentedControlsUI();
            
            // Toggle Joint quick-add fields
            const isJoint = state.dashboardType === 'joint';
            document.getElementById('joint-type-group').classList.toggle('hidden', !isJoint);
            
            updateQuickAddFormFields();
            updateTabTitles();
            renderApp();
        });
    });

    // Segmented View toggles (Calendar vs List)
    document.querySelectorAll('#view-toggle-container .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            state.viewMode = e.target.dataset.mode;
            updateSegmentedControlsUI();
            
            // Toggle sub-views in HTML
            document.getElementById('dashboard-calendar-view').classList.toggle('hidden', state.viewMode === 'list');
            document.getElementById('dashboard-list-view').classList.toggle('hidden', state.viewMode === 'calendar');
            
            renderApp();
        });
    });

    // Segmented List Scope toggles (Month vs Year)
    document.querySelectorAll('#scope-toggle-container .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            state.listScope = e.target.dataset.scope;
            updateSegmentedControlsUI();
            renderApp();
        });
    });

    // Segmented Loans filter toggles (Credit Cards vs Installment Loans)
    document.querySelectorAll('#loans-type-filter-container .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            state.loansFilter = e.target.dataset.filter;
            updateSegmentedControlsUI();
            renderLoansTab();
        });
    });

    // Quick Add transaction type selectors
    document.getElementById('joint-trans-type').addEventListener('change', updateQuickAddFormFields);
    document.getElementById('personal-trans-type').addEventListener('change', updateQuickAddFormFields);
    document.getElementById('contribution-direction').addEventListener('change', updateQuickAddFormFields);

    document.querySelectorAll('[data-savings-mode]').forEach(btn => btn.addEventListener('click', () => {
        state.savingsViewMode = btn.dataset.savingsMode;
        saveDatabase();
        renderSavingsTab();
    }));
    document.querySelectorAll('[data-savings-scope]').forEach(btn => btn.addEventListener('click', () => {
        state.savingsListScope = btn.dataset.savingsScope;
        saveDatabase();
        renderSavingsTab();
    }));

    const updateSavingsEntryForm = () => {
        const isInterest = document.getElementById('savings-entry-type').value === 'interest';
        document.getElementById('savings-entry-amount-label').textContent = isInterest ? 'Interest Amount' : 'Savings Amount';
        document.getElementById('savings-entry-hint').textContent = isInterest
            ? 'Interest affects only Savings and never changes the Personal balance.'
            : 'Positive adds to Savings and subtracts from Personal. Negative does the reverse.';
        document.getElementById('btn-add-savings-entry').textContent = isInterest ? 'Add Monthly Interest' : 'Add Savings Transfer';
        const description = document.getElementById('savings-transfer-description');
        if (isInterest && !description.value.trim()) description.value = 'Monthly Interest';
        if (isInterest) {
            const monthIndex = MONTH_ORDER.indexOf(state.currentMonth);
            const lastDay = String(new Date(state.currentYear, monthIndex + 1, 0).getDate()).padStart(2, '0');
            document.getElementById('savings-transfer-date').value = `${state.currentYear}-${String(monthIndex + 1).padStart(2, '0')}-${lastDay}`;
        }
    };
    document.getElementById('savings-entry-type').addEventListener('change', updateSavingsEntryForm);

    document.getElementById('btn-open-savings-balance').addEventListener('click', () => {
        document.getElementById('savings-current-amount').value = getSavingsStartingBalance().toFixed(2);
        document.getElementById('savings-balance-dialog').showModal();
    });
    document.getElementById('btn-cancel-savings-balance').addEventListener('click', () => document.getElementById('savings-balance-dialog').close());
    document.getElementById('btn-toggle-savings-metrics').addEventListener('click', () => {
        state.savingsMetricsCollapsed = !state.savingsMetricsCollapsed;
        saveDatabase();
        renderSavingsTab();
    });
    document.getElementById('btn-toggle-savings-year').addEventListener('click', () => {
        state.savingsYearSummaryCollapsed = !state.savingsYearSummaryCollapsed;
        saveDatabase();
        renderSavingsTab();
    });
    document.getElementById('btn-toggle-delivery-year').addEventListener('click', () => {
        state.deliveryYearSummaryCollapsed = !state.deliveryYearSummaryCollapsed;
        saveDatabase();
        renderDeliveryTab();
    });
    document.getElementById('btn-expand-all-delivery-summary').addEventListener('click', () => {
        document.querySelectorAll('#delivery-year-summary-content details').forEach(details => {
            details.open = true;
        });
    });
    document.getElementById('btn-collapse-all-delivery-summary').addEventListener('click', () => {
        document.querySelectorAll('#delivery-year-summary-content details').forEach(details => {
            details.open = false;
        });
    });
    document.getElementById('savings-balance-form').addEventListener('submit', event => {
        event.preventDefault();
        const amount = Number(document.getElementById('savings-current-amount').value);
        if (!Number.isFinite(amount)) return;
        state.savingsStartingBalance = amount;
        state.savingsCurrentAmount = amount;
        saveDatabase();
        document.getElementById('savings-balance-dialog').close();
        renderApp();
        logSuccess(`Savings starting balance updated to $${amount.toFixed(2)}.`);
    });
    document.getElementById('savings-transfer-form').addEventListener('submit', event => {
        event.preventDefault();
        const kind = document.getElementById('savings-entry-type').value;
        const date = document.getElementById('savings-transfer-date').value;
        const description = document.getElementById('savings-transfer-description').value.trim();
        const amount = Number(document.getElementById('savings-transfer-amount').value);
        const added = kind === 'interest'
            ? addSavingsInterest(date, description, amount)
            : addLinkedSavingsTransfer(date, description, amount);
        if (!added) return;
        saveDatabase();
        event.currentTarget.reset();
        document.getElementById('savings-transfer-date').value = date;
        updateSavingsEntryForm();
        renderApp();
        logSuccess(kind === 'interest'
            ? `Monthly savings interest added on ${date} without changing Personal.`
            : `Savings transfer added to Savings and Personal on ${date}.`);
    });

    document.getElementById('btn-cancel-savings-edit').addEventListener('click', () => document.getElementById('savings-edit-dialog').close());
    document.getElementById('btn-close-savings-day').addEventListener('click', () => document.getElementById('savings-day-dialog').close());
    document.getElementById('savings-edit-form').addEventListener('submit', event => {
        event.preventDefault();
        const tx = (state.savingsTransactions || []).find(item => item.id === document.getElementById('savings-edit-id').value);
        if (!tx) return;
        const oldKind = tx.kind || 'transfer';
        const newKind = document.getElementById('savings-edit-type').value;
        const amount = Number(document.getElementById('savings-edit-amount').value);
        const date = document.getElementById('savings-edit-date').value;
        const description = document.getElementById('savings-edit-description').value.trim();
        if (!date || !description || !Number.isFinite(amount) || amount === 0) return;
        if (oldKind === 'transfer' && newKind === 'interest') {
            const mirror = findPersonalSavingsMirror(tx.transferId);
            if (mirror) mirror.list.splice(mirror.list.indexOf(mirror.tx), 1);
            tx.personalMirrorDetached = true;
        }
        if (oldKind === 'interest' && newKind === 'transfer') {
            tx.transferId = tx.transferId || 'savings-xfer-' + Math.random().toString(36).substr(2, 9);
            tx.personalMirrorDetached = false;
        }
        tx.kind = newKind;
        tx.savingsTransfer = newKind === 'transfer';
        tx.date = date;
        tx.description = description;
        tx.amount = amount;
        if (newKind === 'transfer') syncSavingsPersonalMirror(tx, oldKind === 'interest');
        saveDatabase();
        document.getElementById('savings-edit-dialog').close();
        renderApp();
        logSuccess(`Updated savings ${newKind}: ${description}.`);
    });
    document.getElementById('btn-delete-savings-edit').addEventListener('click', () => {
        const id = document.getElementById('savings-edit-id').value;
        const tx = (state.savingsTransactions || []).find(item => item.id === id);
        if (!tx || !confirm(`Delete "${tx.description}" from Savings? The Personal ledger will not be changed.`)) return;
        deleteSavingsTransaction(id);
        saveDatabase();
        document.getElementById('savings-edit-dialog').close();
        renderApp();
    });
    // Period selectors change
    const onPeriodChange = () => {
        state.currentYear = parseInt(document.getElementById('year-select').value) || 2026;
        state.currentMonth = document.getElementById('month-select').value;
        state.deliveryWeekIndex = 0;
        
        state.ccYear = state.currentYear;
        state.ccMonth = state.currentMonth;
        
        ensureYearMonthInitialized(state.currentYear, state.currentMonth);
        ensureDeliveryEarningsForMonth(state.currentYear, state.currentMonth);
        
        updateTabTitles();
        renderApp();
    };

    document.getElementById('year-select').addEventListener('change', onPeriodChange);
    document.getElementById('month-select').addEventListener('change', onPeriodChange);
    
    const moveMainCalendar = (offset) => {
        const next = shiftCalendarPeriod(state.currentYear, state.currentMonth, offset);
        state.currentYear = next.year;
        state.currentMonth = next.month;
        state.deliveryWeekIndex = 0;
        
        state.ccYear = state.currentYear;
        state.ccMonth = state.currentMonth;
        
        ensureYearMonthInitialized(next.year, next.month);
        ensureDeliveryEarningsForMonth(next.year, next.month);
        
        document.getElementById('year-select').value = next.year;
        document.getElementById('month-select').value = next.month;
        updateTabTitles();
        renderApp();
    };    document.getElementById('btn-header-prev').addEventListener('click', () => {
        const activeTab = document.querySelector('.nav-btn.active').dataset.tab;
        const isYearScope = (activeTab === 'dashboard' && state.viewMode === 'list' && state.listScope === 'year') ||
                            (activeTab === 'creditcards' && state.ccViewMode === 'list' && state.ccListScope === 'year') ||
                            (activeTab === 'savings' && state.savingsViewMode === 'list' && state.savingsListScope === 'year');
        if (isYearScope) {
            state.currentYear -= 1;
            document.getElementById('year-select').value = state.currentYear;
            state.ccYear = state.currentYear;
            updateTabTitles();
            renderApp();
        } else {
            moveMainCalendar(-1);
        }
    });

    document.getElementById('btn-header-next').addEventListener('click', () => {
        const activeTab = document.querySelector('.nav-btn.active').dataset.tab;
        const isYearScope = (activeTab === 'dashboard' && state.viewMode === 'list' && state.listScope === 'year') ||
                            (activeTab === 'creditcards' && state.ccViewMode === 'list' && state.ccListScope === 'year') ||
                            (activeTab === 'savings' && state.savingsViewMode === 'list' && state.savingsListScope === 'year');
        if (isYearScope) {
            state.currentYear += 1;
            document.getElementById('year-select').value = state.currentYear;
            state.ccYear = state.currentYear;
            updateTabTitles();
            renderApp();
        } else {
            moveMainCalendar(1);
        }
    });

    document.getElementById('btn-header-today').addEventListener('click', () => {
        const today = new Date();
        state.currentYear = today.getFullYear();
        state.currentMonth = MONTH_ORDER[today.getMonth()];
        
        const yearSelect = document.getElementById('year-select');
        const monthSelect = document.getElementById('month-select');
        if (yearSelect) yearSelect.value = state.currentYear;
        if (monthSelect) monthSelect.value = state.currentMonth;
        
        state.ccYear = state.currentYear;
        state.ccMonth = state.currentMonth;
        
        const activeTab = document.querySelector('.nav-btn.active').dataset.tab;
        if (activeTab === 'dashboard') {
            state.viewMode = 'calendar';
            const calBtn = document.querySelector('[data-dashboard-mode="calendar"]');
            if (calBtn) {
                document.querySelectorAll('[data-dashboard-mode]').forEach(btn => btn.classList.remove('active'));
                calBtn.classList.add('active');
            }
        } else if (activeTab === 'creditcards') {
            state.ccViewMode = 'calendar';
            const calBtn = document.querySelector('[data-cc-mode="calendar"]');
            if (calBtn) {
                document.querySelectorAll('[data-cc-mode]').forEach(btn => btn.classList.remove('active'));
                calBtn.classList.add('active');
            }
        } else if (activeTab === 'savings') {
            state.savingsViewMode = 'calendar';
            const calBtn = document.querySelector('[data-savings-mode="calendar"]');
            if (calBtn) {
                document.querySelectorAll('[data-savings-mode]').forEach(btn => btn.classList.remove('active'));
                calBtn.classList.add('active');
            }
        } else if (activeTab === 'delivery') {
            const todayStr = formatLocalDate(today);
            const weeks = getDeliveryWeeksForMonth(state.currentMonth);
            const wIdx = weeks.findIndex(w => w.some(g => g.date === todayStr));
            if (wIdx >= 0) {
                state.deliveryWeekIndex = wIdx;
            } else {
                state.deliveryWeekIndex = 0;
            }
        }
        
        updateTabTitles();
        renderApp();
    });

    // Reset & Backup Buttons
    document.getElementById('btn-reset-data').addEventListener('click', () => {
        if (confirm("Are you sure you want to reset all calculations to the original spreadsheet data? This will overwrite your current changes.")) {
            resetToDefaults();
            
            // Sync UI inputs
            document.getElementById('year-select').value = state.currentYear;
            document.getElementById('month-select').value = state.currentMonth;
            updateSegmentedControlsUI();
            
            // Toggle form views
            const isJoint = state.dashboardType === 'joint';
            document.getElementById('joint-type-group').classList.toggle('hidden', !isJoint);
            document.getElementById('dashboard-calendar-view').classList.toggle('hidden', state.viewMode === 'list');
            document.getElementById('dashboard-list-view').classList.toggle('hidden', state.viewMode === 'calendar');
            updateQuickAddFormFields();
            
            updateTabTitles();
            renderApp();
        }
    });

    document.getElementById('btn-export-data').addEventListener('click', () => {
        const dataStr = "data:text/json;charset=utf-8," + encodeURIComponent(JSON.stringify(state, null, 2));
        const downloadAnchor = document.createElement('a');
        downloadAnchor.setAttribute("href", dataStr);
        downloadAnchor.setAttribute("download", `budgetify_backup_${state.currentYear}_${state.currentMonth}.json`);
        document.body.appendChild(downloadAnchor);
        downloadAnchor.click();
        downloadAnchor.remove();
        logSystem("Backup JSON file exported successfully.");
    });

    // Import JSON file reader
    const triggerImportBtn = document.getElementById('btn-trigger-import');
    const importFileInput = document.getElementById('import-file-input');
    if (triggerImportBtn && importFileInput) {
        triggerImportBtn.addEventListener('click', () => {
            importFileInput.click();
        });
        importFileInput.addEventListener('change', (e) => {
            const file = e.target.files[0];
            if (!file) return;
            const reader = new FileReader();
            reader.onload = (event) => {
                try {
                    const imported = JSON.parse(event.target.result);
                    const validationError = validateImportedDatabase(imported);
                    if (!validationError) {
                        state = imported;
                        saveDatabase();

                        // Re-sync the same UI bits the "Reset to Excel Data" flow does after a full
                        // state replacement, instead of location.reload(). A reload works fine as a
                        // top-level page, but when this app is embedded in an iframe (e.g. a Google
                        // Sites/Drive embed), the sandboxed frame can block the reload's navigation
                        // outright and leave the whole embed blank with no error — renderApp() alone
                        // already picks up every state-driven value, so a hard reload was never
                        // actually necessary for correctness, just a convenient reset-everything shortcut.
                        document.getElementById('year-select').value = state.currentYear;
                        document.getElementById('month-select').value = state.currentMonth;
                        updateSegmentedControlsUI();
                        const isJoint = state.dashboardType === 'joint';
                        document.getElementById('joint-type-group').classList.toggle('hidden', !isJoint);
                        document.getElementById('dashboard-calendar-view').classList.toggle('hidden', state.viewMode === 'list');
                        document.getElementById('dashboard-list-view').classList.toggle('hidden', state.viewMode === 'calendar');
                        updateQuickAddFormFields();
                        updateTabTitles();
                        renderApp();
                        logSuccess("Database successfully imported!");
                    } else {
                        alert(`Invalid backup file: ${validationError}\n\nYour current data was not changed.`);
                    }
                } catch (err) {
                    alert("Error parsing JSON backup file: " + err.message);
                }
            };
            reader.readAsText(file);
        });
    }

    // Quick add transaction form
    document.getElementById('quick-add-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const dateInput = document.getElementById('trans-date').value;
        const descInput = document.getElementById('trans-desc').value;
        
        if (!dateInput || !descInput) return;
        
        const dateObj = new Date(dateInput + 'T00:00:00');
        const y = dateObj.getFullYear();
        const monthShort = MONTH_ORDER[dateObj.getMonth()];
        const key = `${y}-${monthShort}`;
        
        ensureYearMonthInitialized(y, monthShort);
        
        if (state.dashboardType === 'personal') {
            const amountInput = parseFloat(document.getElementById('trans-amount').value);
            if (isNaN(amountInput)) return;
            const personalType = document.getElementById('personal-trans-type').value;
            if (personalType === 'savings-transfer') {
                if (amountInput === 0 || !addLinkedSavingsTransfer(dateInput, descInput, -amountInput)) return;
                logSystem(`Added linked savings transfer on ${dateInput}: Personal ${amountInput >= 0 ? '+' : '-'}$${Math.abs(amountInput).toFixed(2)}, Savings ${amountInput <= 0 ? '+' : '-'}$${Math.abs(amountInput).toFixed(2)}`);
            } else {
                state.personalCalendar[key].push({ id: 'p-' + Math.random().toString(36).substr(2, 9), date: dateInput, description: descInput, amount: amountInput });
                logSystem(`Added personal transaction on ${dateInput}: ${descInput} ($${amountInput.toFixed(2)})`);
            }
        } else if (state.dashboardType === 'joint') {
            // Joint transaction
            const type = document.getElementById('joint-trans-type').value;
            if (type === 'contribution') {
                const direction = document.getElementById('contribution-direction').value;
                const recipient = document.getElementById('contribution-recipient').value;
                let jasonAmt = 0;
                let asiaAmt = 0;
                if (direction === 'deposit') {
                    jasonAmt = Math.abs(parseFloat(document.getElementById('trans-jason-amount').value) || 0);
                    asiaAmt = Math.abs(parseFloat(document.getElementById('trans-asia-amount').value) || 0);
                } else {
                    const withdrawal = Math.abs(parseFloat(document.getElementById('contribution-withdrawal-amount').value) || 0);
                    if (withdrawal <= 0) return;
                    if (recipient === 'jason') jasonAmt = -withdrawal;
                    else asiaAmt = -withdrawal;
                }
                const totalAmt = jasonAmt + asiaAmt;
                if (totalAmt === 0) return;
                const transferId = jasonAmt !== 0 ? 'checking-xfer-' + Math.random().toString(36).substr(2, 9) : '';
                state.jointRegister.push({
                    id: 'j-' + Math.random().toString(36).substr(2, 9), type: 'contribution', name: descInput,
                    jason: jasonAmt, asia: asiaAmt, amount: totalAmt, date: dateInput, transferId,
                    contributionDirection: direction, contributionRecipient: direction === 'withdrawal' ? recipient : ''
                });
                if (jasonAmt !== 0) state.personalCalendar[key].push({
                    id: 'p-' + Math.random().toString(36).substr(2, 9), date: dateInput, description: descInput,
                    amount: -jasonAmt, transferId
                });
                logSystem(`Added joint contribution ${direction} on ${dateInput}: ${descInput} (Jason: $${jasonAmt.toFixed(2)}, Asia: $${asiaAmt.toFixed(2)})`);
            } else {
                const amountInput = parseFloat(document.getElementById('trans-amount').value);
                if (isNaN(amountInput)) return;
                
                state.jointRegister.push({
                    id: 'j-' + Math.random().toString(36).substr(2, 9),
                    type: 'expense',
                    name: descInput,
                    amount: -Math.abs(amountInput),
                    date: dateInput
                });
                
                logSystem(`Added joint expense on ${dateInput}: ${descInput} (-$${Math.abs(amountInput).toFixed(2)})`);
            }
        } else {
            // Credit card transaction
            const amountInput = parseFloat(document.getElementById('trans-amount').value);
            if (isNaN(amountInput)) return;
            
            const cardId = state.dashboardType;
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
            if (!state.cardCalendars[cardId][key]) state.cardCalendars[cardId][key] = [];
            
            state.cardCalendars[cardId][key].push({
                id: 'c-' + Math.random().toString(36).substr(2, 9),
                date: dateInput,
                description: descInput,
                amount: -Math.abs(amountInput)
            });
            adjustCardCurrentBalance(cardId, -Math.abs(amountInput));
            
            logSystem(`Added credit card charge on ${dateInput}: ${descInput} (-$${Math.abs(amountInput).toFixed(2)})`);
        }
        
        saveDatabase();
        renderApp();
        
        // Clear input form
        document.getElementById('trans-desc').value = '';
        document.getElementById('trans-amount').value = '';
        document.getElementById('trans-jason-amount').value = '';
        document.getElementById('trans-asia-amount').value = '';
    });


    // Delivery pagination
    // Delivery pagination crossing month boundaries
    document.getElementById('btn-prev-delivery-week').addEventListener('click', () => {
        if (state.deliveryWeekIndex > 0) {
            state.deliveryWeekIndex--;
            renderDeliveryTab();
        } else {
            let mIdx = MONTH_ORDER.indexOf(state.currentMonth);
            mIdx--;
            if (mIdx < 0) {
                mIdx = 11;
                state.currentYear--;
            }
            state.currentMonth = MONTH_ORDER[mIdx];
            
            const monthSelect = document.getElementById('month-select');
            const yearSelect = document.getElementById('year-select');
            if (monthSelect) monthSelect.value = state.currentMonth;
            if (yearSelect) yearSelect.value = state.currentYear;
            
            const prevWeeks = getDeliveryWeeksForMonth(state.currentMonth);
            state.deliveryWeekIndex = prevWeeks.length > 0 ? prevWeeks.length - 1 : 0;
            
            state.ccYear = state.currentYear;
            state.ccMonth = state.currentMonth;
            
            updateTabTitles();
            renderApp();
        }
    });
    document.getElementById('btn-next-delivery-week').addEventListener('click', () => {
        const weeks = getDeliveryWeeksForMonth(state.currentMonth);
        if (state.deliveryWeekIndex < weeks.length - 1) {
            state.deliveryWeekIndex++;
            renderDeliveryTab();
        } else {
            let mIdx = MONTH_ORDER.indexOf(state.currentMonth);
            mIdx++;
            if (mIdx > 11) {
                mIdx = 0;
                state.currentYear++;
            }
            state.currentMonth = MONTH_ORDER[mIdx];
            
            const monthSelect = document.getElementById('month-select');
            const yearSelect = document.getElementById('year-select');
            if (monthSelect) monthSelect.value = state.currentMonth;
            if (yearSelect) yearSelect.value = state.currentYear;
            
            state.deliveryWeekIndex = 0;
            
            state.ccYear = state.currentYear;
            state.ccMonth = state.currentMonth;
            
            updateTabTitles();
            renderApp();
        }
    });
    document.getElementById('btn-bulk-delivery-budget').addEventListener('click', () => {
        document.getElementById('delivery-budget-form').reset();
        document.getElementById('delivery-bulk-amount-group').style.display = 'block';
        document.getElementById('delivery-bulk-reason-group').style.display = 'none';
        const monthIndex = MONTH_ORDER.indexOf(state.currentMonth);
        document.getElementById('delivery-budget-start').value = formatLocalDate(new Date(state.currentYear, monthIndex, 1));
        document.getElementById('delivery-budget-end').value = formatLocalDate(new Date(state.currentYear, monthIndex + 1, 0));
        document.getElementById('delivery-budget-dialog').showModal();
    });
    document.getElementById('delivery-bulk-action').addEventListener('change', (e) => {
        const val = e.target.value;
        document.getElementById('delivery-bulk-amount-group').style.display = val === 'set-budget' ? 'block' : 'none';
        document.getElementById('delivery-bulk-reason-group').style.display = val === 'mark-off' ? 'block' : 'none';
    });
    document.getElementById('btn-cancel-delivery-budget').addEventListener('click', () => document.getElementById('delivery-budget-dialog').close());
    document.getElementById('delivery-budget-form').addEventListener('submit', event => {
        event.preventDefault();
        const startValue = document.getElementById('delivery-budget-start').value;
        const endValue = document.getElementById('delivery-budget-end').value;
        const action = document.getElementById('delivery-bulk-action').value;
        const amount = Number(document.getElementById('delivery-budget-amount').value);
        const reason = document.getElementById('delivery-budget-reason').value.trim() || 'Off-Day';
        const selectedDays = new Set([...document.querySelectorAll('input[name="delivery-budget-day"]:checked')].map(input => Number(input.value)));
        
        if (!startValue || !endValue || !selectedDays.size) { alert('Choose a date range and at least one weekday.'); return; }
        const start = new Date(startValue + 'T00:00:00');
        const end = new Date(endValue + 'T00:00:00');
        if (end < start) { alert('The ending date cannot be before the starting date.'); return; }
        
        state.deliveryBudgets = state.deliveryBudgets || {};
        let needsSort = false;
        
        for (let date = new Date(start); date <= end; date.setDate(date.getDate() + 1)) {
            if (selectedDays.has(date.getDay())) {
                const dateStr = formatLocalDate(date);
                let rec = state.deliveryEarnings.find(item => item.date === dateStr);
                
                if (action === 'set-budget') {
                    state.deliveryBudgets[dateStr] = amount;
                } else if (action === 'mark-off') {
                    if (!rec) {
                        rec = {
                            date: dateStr,
                            day: ['Sun','Mon','Tue','Wed','Thu','Fri','Sat'][date.getDay()],
                            cash: 0, cashFormula: '',
                            sideGigs: 0, sideGigsFormula: '',
                            grubHub: 0, grubHubFormula: '',
                            uberEats: 0, uberEatsFormula: '',
                            total: 0,
                            noEarnCash: false, noEarnSideGigs: false, noEarnGrubHub: false, noEarnUberEats: false,
                            offDayReason: reason
                        };
                        state.deliveryEarnings.push(rec);
                        needsSort = true;
                    } else {
                        rec.offDayReason = reason;
                        rec.cash = 0; rec.cashFormula = '';
                        rec.sideGigs = 0; rec.sideGigsFormula = '';
                        rec.grubHub = 0; rec.grubHubFormula = '';
                        rec.uberEats = 0; rec.uberEatsFormula = '';
                        rec.total = 0;
                        rec.noEarnCash = false; rec.noEarnSideGigs = false; rec.noEarnGrubHub = false; rec.noEarnUberEats = false;
                    }
                } else if (action === 'reset') {
                    delete state.deliveryBudgets[dateStr];
                    if (rec) {
                        rec.offDayReason = '';
                        rec.cash = 0; rec.cashFormula = '';
                        rec.sideGigs = 0; rec.sideGigsFormula = '';
                        rec.grubHub = 0; rec.grubHubFormula = '';
                        rec.uberEats = 0; rec.uberEatsFormula = '';
                        rec.total = 0;
                        rec.noEarnCash = false; rec.noEarnSideGigs = false; rec.noEarnGrubHub = false; rec.noEarnUberEats = false;
                    }
                }
            }
        }
        
        if (needsSort) {
            state.deliveryEarnings.sort((a,b) => a.date.localeCompare(b.date));
        }
        
        document.getElementById('delivery-budget-dialog').close();
        saveDatabase();
        renderApp();
    });

    document.getElementById('btn-reset-delivery-week').addEventListener('click', () => {
        const weeks = getDeliveryWeeksForMonth(state.currentMonth);
        const activeWeek = weeks[state.deliveryWeekIndex];
        if (!activeWeek || !activeWeek.length) return;
        
        const monStr = new Date(activeWeek[0].date+'T00:00:00').toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
        const sunStr = new Date(activeWeek[activeWeek.length-1].date+'T00:00:00').toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
        
        if (confirm(`Are you sure you want to reset all earnings and budgets for the week of ${monStr} - ${sunStr}? This cannot be undone.`)) {
            activeWeek.forEach(gRecord => {
                const rec = state.deliveryEarnings.find(item => item.date === gRecord.date);
                if (rec) {
                    rec.cash = 0;
                    rec.cashFormula = '';
                    rec.sideGigs = 0;
                    rec.sideGigsFormula = '';
                    rec.grubHub = 0;
                    rec.grubHubFormula = '';
                    rec.uberEats = 0;
                    rec.uberEatsFormula = '';
                    rec.total = 0;
                    rec.noEarnCash = false;
                    rec.noEarnSideGigs = false;
                    rec.noEarnGrubHub = false;
                    rec.noEarnUberEats = false;
                    rec.offDayReason = '';
                }
                if (state.deliveryBudgets) {
                    delete state.deliveryBudgets[gRecord.date];
                }
            });
            saveDatabase();
            renderApp();
            logSystem(`Reset weekly delivery data and budgets for ${monStr} - ${sunStr}`);
        }
    });

    document.getElementById('btn-off-delivery-week').addEventListener('click', () => {
        const weeks = getDeliveryWeeksForMonth(state.currentMonth);
        const activeWeek = weeks[state.deliveryWeekIndex];
        if (!activeWeek || !activeWeek.length) return;

        // Check if all are already off-days to toggle off/on
        const allOff = activeWeek.every(g => g.offDayReason);
        const targetReason = allOff ? '' : 'Off-Day';

        activeWeek.forEach(gRecord => {
            const rec = state.deliveryEarnings.find(item => item.date === gRecord.date);
            if (rec) {
                rec.offDayReason = targetReason;
                if (targetReason) {
                    rec.cash = 0;
                    rec.cashFormula = '';
                    rec.sideGigs = 0;
                    rec.sideGigsFormula = '';
                    rec.grubHub = 0;
                    rec.grubHubFormula = '';
                    rec.uberEats = 0;
                    rec.uberEatsFormula = '';
                    rec.total = 0;
                    rec.noEarnCash = false;
                    rec.noEarnSideGigs = false;
                    rec.noEarnGrubHub = false;
                    rec.noEarnUberEats = false;
                }
            }
        });
        saveDatabase();
        renderApp();
        logSystem(`${targetReason ? 'Marked' : 'Cleared'} weekly off-days for the week.`);
    });

    // Modal Cancels
    document.getElementById('btn-cancel-bill').addEventListener('click', () => {
        document.getElementById('joint-bill-dialog').close();
    });
    document.getElementById('btn-add-manual-transfer').addEventListener('click', () => {
        document.getElementById('manual-transfer-form').reset();
        const monthNumber = String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0');
        const selectedInMonth = state.selectedDate && state.selectedDate.startsWith(`${state.currentYear}-${monthNumber}-`);
        document.getElementById('manual-transfer-date').value = selectedInMonth ? state.selectedDate : `${state.currentYear}-${monthNumber}-01`;
        document.getElementById('manual-transfer-dialog').showModal();
    });
    document.getElementById('btn-cancel-manual-transfer').addEventListener('click', () => document.getElementById('manual-transfer-dialog').close());
    document.getElementById('manual-transfer-form').addEventListener('submit', (event) => {
        event.preventDefault();
        const date = document.getElementById('manual-transfer-date').value;
        const person = document.getElementById('manual-transfer-person').value;
        const description = document.getElementById('manual-transfer-description').value.trim();
        const amount = Number(document.getElementById('manual-transfer-amount').value);
        if (!date || !description || !Number.isFinite(amount) || amount <= 0) return;
        state.manualTransfers = state.manualTransfers || [];
        const transferId = 'manual-transfer-' + Math.random().toString(36).substr(2, 9);
        state.manualTransfers.push({ id: transferId, date, person, description, amount });
        state.jointRegister = state.jointRegister || [];
        state.jointRegister.push({ id: 'j-' + Math.random().toString(36).substr(2, 9), type: 'contribution', name: description, jason: person === 'jason' ? amount : 0, asia: person === 'asia' ? amount : 0, amount, date, transferId, linkedManualTransferId: transferId, planned: true });
        if (person === 'jason') {
            const dateObject = new Date(date + 'T00:00:00');
            const calendarKey = `${dateObject.getFullYear()}-${MONTH_ORDER[dateObject.getMonth()]}`;
            ensureYearMonthInitialized(dateObject.getFullYear(), MONTH_ORDER[dateObject.getMonth()]);
            state.personalCalendar[calendarKey].push({ id: 'p-' + Math.random().toString(36).substr(2, 9), date, description, amount: -amount, transferId, linkedManualTransferId: transferId, planned: true });
        }
        saveDatabase();
        document.getElementById('manual-transfer-dialog').close();
        renderApp();
        logSystem(`Added planned ${person === 'asia' ? 'Asia' : 'Jason'} transfer of $${amount.toFixed(2)} on ${date}.`);
    });
    document.getElementById('btn-cancel-alloc').addEventListener('click', () => {
        document.getElementById('allocation-dialog').close();
    });
    document.getElementById('btn-cancel-loan').addEventListener('click', () => {
        document.getElementById('loan-dialog').close();
    });

    // Bill Splitter item form
    const updateBillFormVisibility = () => {
        const isPersonal = document.getElementById('bill-ownership').value === 'personal';
        const isActual = document.getElementById('bill-entry-type').value === 'actual';
        const sameAmount = document.getElementById('bill-same-payment').checked;
        if (isPersonal) {
            document.getElementById('bill-cycle').value = '1st';
            document.getElementById('bill-budget-frequency').value = 'monthly';
            document.getElementById('bill-charge-frequency').value = 'monthly';
        }
        const budgetMethod = document.getElementById('bill-budget-frequency').value;
        const chargeFrequency = document.getElementById('bill-charge-frequency').value;
        const isSubscription = !isPersonal && chargeFrequency !== 'monthly';
        const isRecurring = document.getElementById('bill-recurring').checked || isSubscription;
        if (isSubscription) document.getElementById('bill-recurring').checked = true;
        const chargeAmount = parseFloat(document.getElementById('bill-amount-field').value) || 0;
        const previewBill = { budgetFrequency: budgetMethod, chargeFrequency, frequencyAmount: chargeAmount, frequencyStartDate: document.getElementById('bill-frequency-start').value, dueDay: Number(document.getElementById('bill-due-day').value) || 1 };
        const occurrences = getBillOccurrenceDates(previewBill, state.currentYear, state.currentMonth).length;
        const monthlyBudget = calculateBillFundingAmount(previewBill, state.currentYear, state.currentMonth);
        document.getElementById('bill-cycle').closest('.form-group').classList.toggle('hidden', isPersonal);
        document.getElementById('bill-budget-frequency').closest('.form-group').classList.toggle('hidden', isPersonal);
        document.getElementById('bill-charge-frequency').closest('.form-group').classList.toggle('hidden', isPersonal);
        document.getElementById('bill-payment-source-group').classList.toggle('hidden', !isActual);
        document.getElementById('bill-due-day-group').classList.toggle('hidden', !isActual || isSubscription);
        // Disabled (not just hidden) whenever inapplicable: dueDay is stored as 0 for "Transfer
        // calculation only" bills, which fails this field's min="1" constraint and silently blocked
        // the Save button via native form validation even though the field wasn't visible.
        document.getElementById('bill-due-day').required = isActual && !isSubscription;
        document.getElementById('bill-due-day').disabled = !isActual || isSubscription;
        document.getElementById('bill-payment-amount-group').classList.toggle('hidden', sameAmount || !isActual);
        if (!sameAmount && isActual) {
            const editId = document.getElementById('bill-edit-id').value;
            if (editId) {
                const currentMonthKey = `${state.currentYear}-${state.currentMonth}`;
                const mBills = state.monthlyBills[currentMonthKey];
                if (mBills) {
                    const foundBill = mBills.cycle1st.bills.find(b => b.id === editId) || mBills.cycle15th.bills.find(b => b.id === editId);
                    if (foundBill && foundBill.isMortgage) {
                        const loan = state.loans.find(l => l.id === foundBill.mortgageLoanId);
                        if (loan) {
                            const pmtAmtInput = document.getElementById('bill-payment-amount');
                            pmtAmtInput.value = Number(loan.monthlyMin).toFixed(2);
                        }
                    }
                }
            }
        }
        document.getElementById('bill-payment-amount-label').textContent = isSubscription ? 'Actual Amount Per Charge' : 'Actual Payment Amount';
        document.getElementById('bill-weekly-day-group').classList.add('hidden');
        document.getElementById('bill-frequency-start-group').classList.toggle('hidden', !isSubscription);
        document.getElementById('bill-recurrence-dates-group').classList.toggle('hidden', !isRecurring);
        document.getElementById('bill-budget-amount-label').textContent = 'Transfer Amount';
        const cyclePreview = document.getElementById('bill-cycle').value === 'both' ? ' • $' + (monthlyBudget / 2).toFixed(2) + ' per semi-monthly cycle' : '';
        document.getElementById('bill-budget-preview').textContent = `${occurrences} scheduled charge${occurrences === 1 ? '' : 's'} this month; transfer budget $${monthlyBudget.toFixed(2)}${cyclePreview}`;
    };    ['bill-entry-type','bill-same-payment','bill-budget-frequency','bill-charge-frequency','bill-weekly-day','bill-frequency-start','bill-due-day','bill-amount-field','bill-cycle','bill-recurring'].forEach(id => document.getElementById(id).addEventListener(id === 'bill-amount-field' ? 'input' : 'change', updateBillFormVisibility));

    document.getElementById('joint-bill-form').addEventListener('submit', (e) => {
        e.preventDefault();

        // Card-payment splitter rows have their own restricted save path: manual rows only accept
        // a transfer-cycle change (amount/date stay managed from Credit Cards/Loans), automatic rows
        // accept the transfer cycle plus the budget fields.
        const cardPmtEditId = document.getElementById('bill-edit-id').value;
        if (cardPmtEditId) {
            const cardPmtMonthKey = `${state.currentYear}-${state.currentMonth}`;
            const cardPmtBills = state.monthlyBills[cardPmtMonthKey];
            const cardPmtRow = cardPmtBills
                ? (cardPmtBills.cycle1st.bills.find(b => b.id === cardPmtEditId) || cardPmtBills.cycle15th.bills.find(b => b.id === cardPmtEditId))
                : null;
            if (cardPmtRow && cardPmtRow.linkedCardPaymentId) {
                const newCycle = document.getElementById('bill-cycle').value;
                if (cardPmtRow.cardPaymentKind !== 'auto') {
                    // Manual card/loan payments: amount and date stay managed under Credit Cards/Loans,
                    // but the transfer cycle used for Bill Splitter allocation can still be changed here.
                    cardPmtRow.cycleAllocation = newCycle;
                    cardPmtRow.userCycleCustomized = true;
                    recalculateBillCycleTotals(cardPmtBills);
                    saveDatabase();
                    renderApp();
                    document.getElementById('joint-bill-dialog').close();
                    logSystem(`Updated transfer cycle for payment: ${cardPmtRow.account}`);
                    return;
                }
                const customAmount = parseFloat(document.getElementById('bill-amount-field').value);
                if (!Number.isFinite(customAmount) || customAmount < 0) {
                    alert('Enter a valid transfer amount.');
                    return;
                }
                cardPmtRow.budgetFrequency = document.getElementById('bill-budget-frequency').value || 'monthly';
                cardPmtRow.frequencyAmount = customAmount;
                cardPmtRow.budgetAmount = customAmount;
                cardPmtRow.amount = -customAmount;
                cardPmtRow.samePaymentAmount = document.getElementById('bill-same-payment').checked;
                cardPmtRow.userBudgetCustomized = true;
                cardPmtRow.cycleAllocation = newCycle;
                cardPmtRow.userCycleCustomized = true;
                // Automatic payments recur every month, so the cycle choice is saved on the card/loan
                // itself (not just this month's row) — syncCardPaymentSplitterRowsForMonth reads it
                // when generating every future month's row, so the change applies going forward too.
                const cardPmtTarget = state.loans.find(l => l.id === cardPmtRow.payoffTargetId);
                if (cardPmtTarget) cardPmtTarget.splitterCycleOverride = newCycle;
                recalculateBillCycleTotals(cardPmtBills);
                saveDatabase();
                renderApp();
                document.getElementById('joint-bill-dialog').close();
                logSystem(`Updated budget for automatic card payment: ${cardPmtRow.account}`);
                return;
            }
        }

        const name = document.getElementById('bill-name').value.trim();
        const ownership = document.getElementById('bill-ownership').value || 'joint';
        const isPersonalExpense = ownership === 'personal';
        const cycle = isPersonalExpense ? '1st' : document.getElementById('bill-cycle').value;
        const cycleKey = cycle === '15th' ? 'cycle15th' : 'cycle1st';
        const budgetFrequency = isPersonalExpense ? 'monthly' : document.getElementById('bill-budget-frequency').value;
        const chargeFrequency = isPersonalExpense ? 'monthly' : document.getElementById('bill-charge-frequency').value;
        const frequencyAmount = parseFloat(document.getElementById('bill-amount-field').value);
        const frequencyStartDate = document.getElementById('bill-frequency-start').value;
        const weeklyDay = Number(document.getElementById('bill-weekly-day').value);
        const previewBill = { budgetFrequency, chargeFrequency, frequencyAmount, frequencyStartDate, dueDay: Number(document.getElementById('bill-due-day').value) || 1 };
        const previewOccurrences = getBillOccurrenceDates(previewBill, state.currentYear, state.currentMonth).length;
        const budgetAmount = calculateBillFundingAmount(previewBill, state.currentYear, state.currentMonth);
        const samePaymentAmount = document.getElementById('bill-same-payment').checked;
        const entryType = document.getElementById('bill-entry-type').value;
        const enteredPayment = parseFloat(document.getElementById('bill-payment-amount').value);
        const occurrencePaymentAmount = entryType === 'actual' ? (samePaymentAmount ? frequencyAmount : enteredPayment) : 0;
        const paymentAmount = entryType === 'actual' ? occurrencePaymentAmount * previewOccurrences : 0;
        const dueDay = entryType === 'actual' ? (parseInt(document.getElementById('bill-due-day').value) || (cycle === '1st' ? 1 : 15)) : 0;
        const paymentSource = ownership === 'personal'
            ? 'personalChecking'
            : (document.getElementById('bill-payment-source').value || 'jointChecking');
        const isRecurring = document.getElementById('bill-recurring').checked || chargeFrequency !== 'monthly';
        // Start/End are full calendar dates; recurringStartMonth/recurringEndMonth are derived from
        // them so the existing month-granularity recurrence machinery (templates, propagation,
        // recurrence indexes) keeps working, while the *Date fields add day-level occurrence
        // filtering within the first/final month.
        const selectedRecurringStart = document.getElementById('bill-recurring-start').value;
        const recurringStartDate = isRecurring ? (chargeFrequency !== 'monthly' && frequencyStartDate ? frequencyStartDate : selectedRecurringStart) : '';
        const recurringStartMonth = recurringStartDate ? recurringStartDate.slice(0, 7) : '';
        const recurringEndDate = isRecurring ? document.getElementById('bill-recurring-end').value : '';
        const recurringEndMonth = recurringEndDate ? recurringEndDate.slice(0, 7) : '';
        const editId = document.getElementById('bill-edit-id').value;
        const oldCycleKey = document.getElementById('bill-edit-cycle').value;

        if (chargeFrequency !== 'monthly' && !frequencyStartDate) { alert('Select a subscription start date.'); return; }

        if (!name || !Number.isFinite(budgetAmount) || budgetAmount < 0 || (entryType === 'actual' && (!Number.isFinite(paymentAmount) || paymentAmount < 0))) {
            alert('Enter valid transfer-budget and payment amounts.');
            return;
        }

        if (isRecurring && recurringStartMonth && recurringEndMonth && getBillRecurrenceMonthIndex(recurringEndMonth) < getBillRecurrenceMonthIndex(recurringStartMonth)) {
            alert('The final payment month cannot be before the recurring start month.');
            return;
        }
        const key = `${state.currentYear}-${state.currentMonth}`;
        ensureYearMonthInitialized(state.currentYear, state.currentMonth);
        const mBills = state.monthlyBills[key];
        let existing = null;
        if (editId && oldCycleKey && mBills[oldCycleKey]) {
            const oldIndex = mBills[oldCycleKey].bills.findIndex(item => item.id === editId);
            if (oldIndex > -1) existing = mBills[oldCycleKey].bills.splice(oldIndex, 1)[0];
            removeBillLedgerEntries(editId, state.currentYear, state.currentMonth, existing);
        }

        const bill = normalizeBillSplitterItem({
            ...existing,
            id: existing?.id || 'bill-' + Math.random().toString(36).substr(2, 9),
            recurringSeriesId: existing?.recurringSeriesId || (isRecurring ? existing?.id || 'bill-series-' + Math.random().toString(36).substr(2, 9) : ''),
            account: name,
            category: document.getElementById('bill-category').value || 'bill',
            budgetAmount,
            paymentAmount,
            samePaymentAmount,
            amount: -Math.abs(budgetAmount),
            dueDay,
            paymentSource,
            entryType,
            ownership,
            cycleAllocation: cycle,
            budgetFrequency,
            chargeFrequency,
            frequencyAmount,
            frequencyStartDate,
            occurrencePaymentAmount,
            weeklyAmount: frequencyAmount,
            weeklyDay,
            weeklyOccurrences: previewOccurrences,
            isRecurring,
            recurringStartMonth,
            recurringStartDate,
            recurringEndMonth,
            recurringEndDate,
            manualTransferAmount: (existing && existing.isMortgage) ? frequencyAmount : (existing?.manualTransferAmount ?? frequencyAmount),
            manualSamePaymentAmount: (existing && existing.isMortgage) ? samePaymentAmount : (existing?.manualSamePaymentAmount ?? samePaymentAmount),
            manualOccurrencePaymentAmount: (existing && existing.isMortgage) ? occurrencePaymentAmount : (existing?.manualOccurrencePaymentAmount ?? occurrencePaymentAmount)
        }, cycleKey);
        if (isBillActiveForPeriod(bill, state.currentYear, state.currentMonth)) {
            mBills[cycleKey].bills.push(bill);
            syncBillLedgerEntry(bill, state.currentYear, state.currentMonth);
        }
        recalculateBillCycleTotals(mBills);
        propagateRecurringBillChanges(bill, state.currentYear, state.currentMonth, existing);

        saveDatabase();
        renderApp();
        document.getElementById('joint-bill-dialog').close();
        logSystem(`${existing ? 'Updated' : 'Added'} Bill Splitter item: ${name}`);
    });

    // Allocation Modal Submit
    const getAllocationOccurrenceCount = (frequency, startDate, year, month) => {
        const monthIndex = MONTH_ORDER.indexOf(month);
        if (monthIndex < 0) return 0;
        const first = new Date(Number(year), monthIndex, 1);
        const last = new Date(Number(year), monthIndex + 1, 0);
        const start = startDate ? new Date(`${startDate}T00:00:00`) : first;
        if (Number.isNaN(start.getTime()) || last < start) return 0;
        if (frequency === 'yearly') return first.getMonth() === start.getMonth() && first.getFullYear() >= start.getFullYear() ? 1 : 0;
        if (frequency !== 'weekly') return 1;
        let count = 0;
        for (let day = 1; day <= last.getDate(); day++) {
            const date = new Date(Number(year), monthIndex, day);
            if (date >= start && date.getDay() === start.getDay()) count++;
        }
        return count;
    };
    const updateAllocationFrequencyPreview = () => {
        const frequency = document.getElementById('alloc-frequency').value;
        const startDate = document.getElementById('alloc-start-date').value;
        const count = getAllocationOccurrenceCount(frequency, startDate, state.currentYear, state.currentMonth);
        const labels = { weekly: 'weekly occurrences', monthly: 'monthly occurrence', yearly: 'yearly occurrence' };
        document.getElementById('alloc-frequency-preview').textContent = `${count} ${labels[frequency]} in ${MONTH_NAMES[state.currentMonth]}; entered amounts are applied ${count} time${count === 1 ? '' : 's'}.`;
    };
    document.getElementById('alloc-frequency').addEventListener('change', updateAllocationFrequencyPreview);
    document.getElementById('alloc-start-date').addEventListener('change', updateAllocationFrequencyPreview);    const readOptionalAllocationAmount = id => {
        const raw = document.getElementById(id).value.trim();
        if (raw === '') return null;
        const value = Number(raw);
        return Number.isFinite(value) ? value : NaN;
    };
    document.getElementById('alloc-offset-enabled').addEventListener('change', (e) => {
        document.getElementById('alloc-offset-fields').classList.toggle('hidden', !e.target.checked);
        if (e.target.checked) {
            if (!document.getElementById('alloc-offset-jason').value) document.getElementById('alloc-offset-jason').value = document.getElementById('alloc-jason').value;
            if (!document.getElementById('alloc-offset-asia').value) document.getElementById('alloc-offset-asia').value = document.getElementById('alloc-asia').value;
        }
    });
    // Per-person checkboxes reveal the amount field; unchecking clears it so a hidden field never
    // silently contributes an amount on save.
    [['alloc-jason-enabled', 'alloc-jason-group', 'alloc-jason'], ['alloc-asia-enabled', 'alloc-asia-group', 'alloc-asia']].forEach(([cbId, groupId, inputId]) => {
        document.getElementById(cbId).addEventListener('change', (e) => {
            document.getElementById(groupId).classList.toggle('hidden', !e.target.checked);
            if (!e.target.checked) document.getElementById(inputId).value = '';
        });
    });
    document.getElementById('alloc-recurring').addEventListener('change', (e) => {
        document.getElementById('alloc-recurrence-dates-group').classList.toggle('hidden', !e.target.checked);
    });
    document.getElementById('allocation-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const name = document.getElementById('alloc-name').value.trim();
        const cycle = document.getElementById('alloc-cycle').value;
        const isRecurringAlloc = document.getElementById('alloc-recurring').checked;
        // Frequency/start date only apply to recurring allocations; a one-time allocation lands in
        // the currently viewed month's chosen cycle with no schedule.
        const frequency = isRecurringAlloc ? document.getElementById('alloc-frequency').value : 'monthly';
        const startDate = isRecurringAlloc ? document.getElementById('alloc-start-date').value : '';
        const occurrenceCount = getAllocationOccurrenceCount(frequency, startDate, state.currentYear, state.currentMonth);
        const jasonEnabled = document.getElementById('alloc-jason-enabled').checked;
        const asiaEnabled = document.getElementById('alloc-asia-enabled').checked;
        const jasonInput = jasonEnabled ? readOptionalAllocationAmount('alloc-jason') : null;
        const asiaInput = asiaEnabled ? readOptionalAllocationAmount('alloc-asia') : null;
        const offsetEnabled = document.getElementById('alloc-offset-enabled').checked;
        const offsetJasonInput = readOptionalAllocationAmount('alloc-offset-jason');
        const offsetAsiaInput = readOptionalAllocationAmount('alloc-offset-asia');
        const applyFuture = isRecurringAlloc;
        const allocEndDate = isRecurringAlloc ? document.getElementById('alloc-end-date').value : '';
        const editId = document.getElementById('alloc-edit-id').value;
        const editCycleKey = document.getElementById('alloc-edit-cycle').value;
        if (!name || [jasonInput, asiaInput, offsetJasonInput, offsetAsiaInput].some(Number.isNaN)) return;
        if (isRecurringAlloc && (frequency === 'weekly' || frequency === 'yearly') && !startDate) { alert('Select a start date for this allocation frequency.'); return; }
        if (!editId && jasonInput === null && asiaInput === null) { alert('Check Jason, Asia, or both and enter an amount.'); return; }

        ensureYearMonthInitialized(state.currentYear, state.currentMonth);
        const key = `${state.currentYear}-${state.currentMonth}`;
        const mBills = state.monthlyBills[key];
        let existing = null;
        if (editId && editCycleKey) {
            const list = mBills[editCycleKey].contributions;
            const index = list.findIndex(item => item.id === editId);
            if (index > -1) existing = list.splice(index, 1)[0];
        }
        const resolvedSourceJason = jasonInput === null ? (existing?.sourceJason ?? existing?.jason ?? null) : jasonInput;
        const resolvedSourceAsia = asiaInput === null ? (existing?.sourceAsia ?? existing?.asia ?? null) : asiaInput;
        const resolvedJason = resolvedSourceJason === null ? null : resolvedSourceJason * occurrenceCount;
        const resolvedAsia = resolvedSourceAsia === null ? null : resolvedSourceAsia * occurrenceCount;
        const seriesId = existing?.seriesId || 'alloc-series-' + Math.random().toString(36).substr(2, 9);
        const role = existing?.role || 'base';
        // 'both' allocations are stored once in cycle1st with cycle:'both'; the cycle totals split
        // their amounts half/half across the two cycles (see getAllocationCycleTotal).
        const cycleKey = cycle === '15th' ? 'cycle15th' : 'cycle1st';
        const allocation = { id: existing?.id || 'alloc-' + Math.random().toString(36).substr(2, 9), seriesId, role, name, jason: resolvedJason, asia: resolvedAsia, sourceJason: resolvedSourceJason, sourceAsia: resolvedSourceAsia, cycle, frequency, startDate, occurrenceCount };
        if (occurrenceCount > 0) mBills[cycleKey].contributions.push(allocation);

        if (offsetEnabled && !existing) {
            // For 'both'-cycle allocations the offset lands in the 15th cycle (same as a 1st-cycle base).
            const next = cycle !== '15th' ? { year: state.currentYear, month: state.currentMonth, cycle: '15th', cycleKey: 'cycle15th' } : { ...shiftCalendarPeriod(state.currentYear, state.currentMonth, 1), cycle: '1st', cycleKey: 'cycle1st' };
            ensureYearMonthInitialized(next.year, next.month);
            const offsetJason = offsetJasonInput === null ? resolvedJason : offsetJasonInput;
            const offsetAsia = offsetAsiaInput === null ? resolvedAsia : offsetAsiaInput;
            state.monthlyBills[`${next.year}-${next.month}`][next.cycleKey].contributions.push({ id: 'alloc-' + Math.random().toString(36).substr(2, 9), seriesId, role: 'offset', name, jason: offsetJason, asia: offsetAsia, cycle: next.cycle });
        }

        if (applyFuture) {
            // startIndex marks the month BEFORE the first auto-generated month (template generation
            // is `targetIndex <= startIndex ? skip`). Derived from the Start Date's month when set
            // (allocations can start in a future month); default stays "generate from next month on"
            // since the current month's occurrence is pushed directly above.
            let startIndex = state.currentYear * 12 + MONTH_ORDER.indexOf(state.currentMonth);
            if (startDate) {
                const sd = new Date(startDate + 'T00:00:00');
                if (!Number.isNaN(sd.getTime())) startIndex = sd.getFullYear() * 12 + sd.getMonth() - 1;
            }
            const template = state.allocationTemplates[seriesId] || { seriesId, startIndex };
            if (startDate) template.startIndex = startIndex;
            template.endDate = allocEndDate || '';
            if (role === 'offset') {
                if (jasonInput !== null) template.offsetJason = jasonInput;
                if (asiaInput !== null) template.offsetAsia = asiaInput;
                template.offsetEnabled = true;
            } else {
                template.name = name; template.cycle = cycle; template.frequency = frequency; template.startDate = startDate;
                if (jasonInput !== null || !existing) template.jason = resolvedSourceJason;
                if (asiaInput !== null || !existing) template.asia = resolvedSourceAsia;
                if (offsetEnabled) {
                    template.offsetEnabled = true;
                    if (offsetJasonInput !== null) template.offsetJason = offsetJasonInput;
                    else if (template.offsetJason === undefined) template.offsetJason = resolvedSourceJason;
                    if (offsetAsiaInput !== null) template.offsetAsia = offsetAsiaInput;
                    else if (template.offsetAsia === undefined) template.offsetAsia = resolvedSourceAsia;
                }
            }
            template.signedValues = true;
            state.allocationTemplates[seriesId] = template;
            updateFutureAllocationOccurrences(seriesId, role, state.currentYear, state.currentMonth, { name, cycle, jason: jasonInput, asia: asiaInput });
        }
        recalculateBillCycleTotals(mBills);
        saveDatabase(); renderApp(); document.getElementById('allocation-dialog').close();
        logSystem(`${existing ? 'Updated' : 'Added'} personal allocation: ${name}`);
    });    document.getElementById('btn-cancel-seasonal').addEventListener('click', () => document.getElementById('seasonal-dialog').close());
    document.getElementById('seasonal-recurring').addEventListener('change', (e) => document.getElementById('seasonal-frequency-group').classList.toggle('hidden', !e.target.checked));
    document.getElementById('seasonal-has-charge').addEventListener('change', (e) => document.getElementById('seasonal-charge-group').classList.toggle('hidden', !e.target.checked));
    document.getElementById('seasonal-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const editId = document.getElementById('seasonal-edit-id').value;
        const name = document.getElementById('seasonal-name').value.trim();
        const amount = parseFloat(document.getElementById('seasonal-amount').value);
        const cycles = parseInt(document.getElementById('seasonal-cycles').value);
        const startDate = document.getElementById('seasonal-start-date').value;
        const endDate = document.getElementById('seasonal-end-date').value;
        const isRecurring = document.getElementById('seasonal-recurring').checked;
        const frequency = document.getElementById('seasonal-frequency').value;
        const hasCharge = document.getElementById('seasonal-has-charge').checked;
        const chargeAmount = parseFloat(document.getElementById('seasonal-charge-amount').value);
        const chargeDate = document.getElementById('seasonal-charge-date').value;
        const chargeSource = document.getElementById('seasonal-charge-source').value;
        if (!name || !Number.isFinite(amount) || amount <= 0 || !Number.isInteger(cycles) || !startDate) return;
        if (endDate && endDate < startDate) { alert('End date cannot be before the start date.'); return; }
        if (hasCharge && (!Number.isFinite(chargeAmount) || chargeAmount <= 0 || !chargeDate)) { alert('Enter a charge amount and charge date, or uncheck "has an actual charge".'); return; }
        const id = editId || 'seasonal-' + Math.random().toString(36).substr(2, 9);
        removeSeasonalInstallments(id);
        const definition = { id, name, amount, startDate, endDate, cycles: Math.min(48, Math.max(1, cycles)), isRecurring, frequency, hasCharge, chargeAmount: hasCharge ? chargeAmount : undefined, chargeDate: hasCharge ? chargeDate : undefined, chargeSource: hasCharge ? chargeSource : undefined };
        const index = state.seasonalExpenses.findIndex(item => item.id === id);
        if (index > -1) state.seasonalExpenses[index] = definition; else state.seasonalExpenses.push(definition);
        applySeasonalExpensesForMonth(state.currentYear, state.currentMonth);
        applySeasonalChargeForMonth(state.currentYear, state.currentMonth);
        saveDatabase(); renderApp(); document.getElementById('seasonal-dialog').close();
    });
    // Loan Dialog Submit
    // Toggle loan promos and limit sections based on type
    const updateChargeCardFields = () => {
        const isCredit = document.getElementById('loan-type-field').value === 'credit';
        const isChargeCard = isCredit && document.getElementById('loan-is-charge-card').checked;
        document.getElementById('loan-charge-card-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-limit-group').classList.toggle('hidden', !isCredit || isChargeCard);
    };
    document.getElementById('loan-is-charge-card').addEventListener('change', updateChargeCardFields);
    document.getElementById('loan-type-field').addEventListener('change', (e) => {
        const isCredit = e.target.value === 'credit';
        document.getElementById('loan-purchase-promo-section').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-payment-plans-section').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-payment-strategy-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-limit-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-xfer-section').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-statement-day-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-mortgage-section').classList.toggle('hidden', isCredit);
    });

    const updateMortgageMinimumPayment = () => {
        const isMortgage = document.getElementById('loan-is-mortgage').checked;
        const type = document.getElementById('loan-type-field').value;
        if (type === 'loan' && isMortgage) {
            const escrow = parseFloat(document.getElementById('loan-mortgage-escrow').value) || 0;
            const pi = parseFloat(document.getElementById('loan-mortgage-pi').value) || 0;
            const extra = parseFloat(document.getElementById('loan-mortgage-extra').value) || 0;
            document.getElementById('loan-monthly-min').value = (escrow + pi + extra).toFixed(2);
        }
    };

    document.getElementById('loan-is-mortgage').addEventListener('change', (e) => {
        document.getElementById('loan-mortgage-fields').classList.toggle('hidden', !e.target.checked);
        updateMortgageMinimumPayment();
    });

    ['loan-mortgage-escrow', 'loan-mortgage-pi', 'loan-mortgage-extra'].forEach(id => {
        document.getElementById(id).addEventListener('input', updateMortgageMinimumPayment);
    });

    // Toggle active promo purchase rate inputs
    document.getElementById('loan-purchase-promo-active').addEventListener('change', (e) => {
        document.getElementById('loan-purchase-promo-fields').classList.toggle('hidden', !e.target.checked);
    });

    // Toggle recurring charge day fields in quick-add form
    document.getElementById('cc-trans-recurring').addEventListener('change', (e) => {
        document.getElementById('cc-recurring-day-group').classList.toggle('hidden', !e.target.checked);
    });
    document.getElementById('cc-trans-kind').addEventListener('change', (e) => {
        const isCredit = e.target.value === 'credit';
        document.getElementById('cc-recurring-options').classList.toggle('hidden', isCredit);
        if (isCredit) {
            document.getElementById('cc-trans-recurring').checked = false;
            document.getElementById('cc-recurring-day-group').classList.add('hidden');
        }
    });

    // Toggle recurring charge day fields in edit dialog
    document.getElementById('edit-tx-recurring').addEventListener('change', (e) => {
        document.getElementById('edit-recurring-day-group').classList.toggle('hidden', !e.target.checked);
    });

    document.getElementById('edit-tx-kind').addEventListener('change', (e) => {
        const isCharge = e.target.value === 'charge';
        document.getElementById('edit-recurring-group').classList.toggle('hidden', !isCharge);
        document.getElementById('edit-payment-plan-group').classList.toggle('hidden', !isCharge);
        if (!isCharge) {
            document.getElementById('edit-tx-recurring').checked = false;
            document.getElementById('edit-recurring-day-group').classList.add('hidden');
            document.getElementById('edit-tx-payment-plan').checked = false;
            document.getElementById('edit-payment-plan-fields').classList.add('hidden');
        }
    });

    document.getElementById('edit-tx-payment-plan').addEventListener('change', (e) => {
        document.getElementById('edit-payment-plan-fields').classList.toggle('hidden', !e.target.checked);
        if (e.target.checked && !document.getElementById('edit-plan-current').value) {
            document.getElementById('edit-plan-current').value = Math.abs(parseFloat(document.getElementById('edit-tx-amount').value) || 0);
        }
    });

    document.getElementById('btn-add-existing-plan').addEventListener('click', () => {
        const original = parseFloat(document.getElementById('existing-plan-original').value);
        const current = parseFloat(document.getElementById('existing-plan-current').value);
        const payment = parseFloat(document.getElementById('existing-plan-payment').value);
        const remainingPayments = parseInt(document.getElementById('existing-plan-remaining-payments').value);
        if (![original, current, payment].every(Number.isFinite) || original <= 0 || current < 0 || payment <= 0 || (Number.isFinite(remainingPayments) && remainingPayments < 0)) {
            alert('Enter valid original amount, current balance, monthly principal payment, and remaining payments.');
            return;
        }
        const existing = tempEditingPaymentPlans.find(plan => plan.id === editingPaymentPlanId);
        const plan = normalizePaymentPlan({
            id: existing?.id,
            sourceTransactionId: existing?.sourceTransactionId,
            name: document.getElementById('existing-plan-name').value.trim() || 'Existing Plan',
            originalAmount: original,
            currentBalance: current,
            lengthMonths: parseInt(document.getElementById('existing-plan-length').value) || Math.ceil(current / payment),
            remainingPayments: Number.isFinite(remainingPayments) ? remainingPayments : Math.ceil(current / payment),
            monthlyPayment: payment,
            monthlyFee: parseFloat(document.getElementById('existing-plan-fee').value) || 0,
            startDate: document.getElementById('existing-plan-activated').value || formatLocalDate(new Date())
        });
        if (existing) tempEditingPaymentPlans = tempEditingPaymentPlans.map(item => item.id === existing.id ? plan : item);
        else tempEditingPaymentPlans.push(plan);
        renderEditingPaymentPlans();
        resetExistingPlanEditor();
    });

    document.getElementById('btn-cancel-plan-edit').addEventListener('click', resetExistingPlanEditor);

    // Balance transfer entry mode and save handler
    document.getElementById('xfer-mode').addEventListener('change', updateBalanceTransferModeFields);
    document.getElementById('btn-execute-xfer').addEventListener('click', () => {
        const mode = document.getElementById('xfer-mode').value;
        const amount = parseFloat(document.getElementById('xfer-amount').value);
        const currentBalance = parseFloat(document.getElementById('xfer-current-balance').value);
        const sourceId = document.getElementById('xfer-source').value;
        const feePct = parseFloat(document.getElementById('xfer-fee-pct').value) || 0;
        const rate = parseFloat(document.getElementById('xfer-promo-rate').value) || 0;
        const expDate = document.getElementById('xfer-promo-exp').value;
        const transferOwner = document.getElementById('xfer-owner').value;
        const targetId = document.getElementById('loan-edit-id').value;

        if (mode === 'existing') {
            if (!Number.isFinite(amount) || amount <= 0 || !Number.isFinite(currentBalance) || currentBalance < 0 || currentBalance > amount || !expDate) {
                alert('Enter a valid original amount, current balance, and expiration date. Current balance cannot exceed the original amount.');
                return;
            }
            recordExistingBalanceTransfer(targetId, amount, currentBalance, rate, expDate, transferOwner);
        } else {
            if (!Number.isFinite(amount) || amount <= 0 || !sourceId || !expDate) {
                alert('Please fill in a valid transfer amount, source account, and expiration date.');
                return;
            }
            if (!confirm(`Are you sure you want to transfer ${amount.toFixed(2)} from the selected account to this card?`)) return;
            executeBalanceTransfer(targetId, sourceId, amount, feePct, rate, expDate, transferOwner);
        }

        document.getElementById('xfer-amount').value = '';
        document.getElementById('xfer-current-balance').value = '';
        document.getElementById('xfer-fee-pct').value = '3.0';
        document.getElementById('xfer-promo-rate').value = '0';
        document.getElementById('xfer-promo-exp').value = '';
    });

    // Loan Dialog Submit (Handles Add & Edit)
    document.getElementById('loan-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const action = document.getElementById('loan-action').value;
        const editId = document.getElementById('loan-edit-id').value;
        
        const name = document.getElementById('loan-name-field').value;
        const type = document.getElementById('loan-type-field').value;
        const start = parseFloat(document.getElementById('loan-start-bal').value);
        const current = parseFloat(document.getElementById('loan-current-bal').value);
        const rate = parseFloat(document.getElementById('loan-interest-rate').value) || 0;
        const due = parseInt(document.getElementById('loan-due-day').value) || 15;
        const statementDay = parseInt(document.getElementById('loan-statement-day').value) || 1;
        const monthly = parseFloat(document.getElementById('loan-monthly-min').value);
        const isChargeCard = type === 'credit' && document.getElementById('loan-is-charge-card').checked;
        const limit = isChargeCard ? null : (parseFloat(document.getElementById('loan-limit-field').value) || start);
        
        const promoActive = document.getElementById('loan-purchase-promo-active').checked;
        const promoRate = parseFloat(document.getElementById('loan-purchase-promo-rate').value) || 0;
        const promoExpDate = document.getElementById('loan-purchase-promo-exp').value;
        const paymentStrategy = type === 'credit' ? document.getElementById('loan-payment-strategy').value : 'none';
        const paymentSource = document.getElementById('loan-payment-source').value;
        const paymentEndDate = document.getElementById('loan-payment-end-date').value;
        const firstPaymentDate = document.getElementById('loan-first-payment-date').value;
        const splitterCycleOverride = document.getElementById('loan-splitter-cycle').value;
        const isExemptFromSplitter = document.getElementById('loan-exempt-splitter').checked;
        
        const isMortgage = type === 'loan' && document.getElementById('loan-is-mortgage').checked;
        const escrowAmount = isMortgage ? (parseFloat(document.getElementById('loan-mortgage-escrow').value) || 0) : 0;
        const piAmount = isMortgage ? (parseFloat(document.getElementById('loan-mortgage-pi').value) || 0) : 0;
        const extraPayment = isMortgage ? (parseFloat(document.getElementById('loan-mortgage-extra').value) || 0) : 0;
        
        let adjustedMonthly = monthly;
        if (isMortgage) {
            adjustedMonthly = escrowAmount + piAmount + extraPayment;
        }

        if (!name || isNaN(start) || isNaN(current) || isNaN(adjustedMonthly)) return;
        
        if (action === 'edit') {
            const loan = state.loans.find(l => l.id === editId);
            if (loan) {
                loan.name = name;
                loan.type = type;
                loan.startBal = start;
                loan.currentBal = current;
                loan.interestRate = rate;
                loan.dueDay = due;
                loan.statementDay = statementDay;
                loan.monthlyMin = adjustedMonthly;
                loan.limit = limit;
                loan.isChargeCard = isChargeCard;
                loan.promoActive = promoActive;
                loan.promoRate = promoRate;
                loan.promoExpDate = promoExpDate;
                loan.promos = JSON.parse(JSON.stringify(tempEditingPromos));
                clearFutureAutomaticCardPayments(loan.id);
                loan.paymentPlans = JSON.parse(JSON.stringify(tempEditingPaymentPlans));
                loan.paymentStrategy = paymentStrategy;
                loan.paymentSource = paymentSource;
                loan.paymentStrategyStartDate = firstPaymentDate || formatLocalDate(new Date());
                loan.paymentEndDate = paymentEndDate;
                loan.splitterCycleOverride = splitterCycleOverride;
                
                loan.isMortgage = isMortgage;
                loan.escrowAmount = escrowAmount;
                loan.piAmount = piAmount;
                loan.extraPayment = extraPayment;
                loan.isExemptFromSplitter = isExemptFromSplitter;
                
                logSystem(`Updated payoff target: ${name}`);
            }
        } else {
            const id = name.toLowerCase().replace(/[^a-z0-9]/g, '_');
            state.loans.push({
                id: id,
                name: name,
                type: type,
                startBal: start,
                currentBal: current,
                interestRate: rate,
                dueDay: due,
                statementDay: statementDay,
                monthlyMin: adjustedMonthly,
                limit: limit,
                isChargeCard: isChargeCard,
                promoActive: promoActive,
                promoRate: promoRate,
                promoExpDate: promoExpDate,
                promos: JSON.parse(JSON.stringify(tempEditingPromos)),
                paymentPlans: JSON.parse(JSON.stringify(tempEditingPaymentPlans)),
                paymentStrategy: paymentStrategy,
                paymentSource: paymentSource,
                paymentStrategyStartDate: firstPaymentDate || formatLocalDate(new Date()),
                paymentEndDate: paymentEndDate,
                splitterCycleOverride: splitterCycleOverride,
                
                isMortgage: isMortgage,
                escrowAmount: escrowAmount,
                piAmount: piAmount,
                extraPayment: extraPayment,
                isExemptFromSplitter: isExemptFromSplitter
            });
            logSystem(`Added payoff target: ${name} (Balance: $${current.toFixed(2)})`);
        }
        
        syncMortgageLoansToAllMonths();
        saveDatabase();
        renderApp();
        document.getElementById('loan-dialog').close();
    });

    // Open proposed payment dialog (add mode) — shared by the Credit Cards and Loans tabs' "+ Add
    // Proposed Payment" buttons, each tagged with data-target-type so the dropdown only shows that
    // tab's own targets (credit cards don't leak into the loans dropdown and vice versa).
    document.querySelectorAll('#btn-add-proposed-payment, #btn-add-proposed-loan-payment').forEach(btn => {
        btn.addEventListener('click', (e) => {
            const targetType = e.currentTarget.dataset.targetType || 'credit';
            document.getElementById('proposed-payment-form').reset();
            document.getElementById('prop-pay-action').value = 'add';
            document.getElementById('prop-pay-edit-id').value = '';
            document.getElementById('prop-pay-link-id').value = '';
            document.getElementById('prop-pay-type').value = targetType;
            document.getElementById('prop-pay-date').value = state.selectedDate;
            document.querySelector('#proposed-payment-form h3').textContent = 'Add Proposed Future Payment';
            document.querySelector('#proposed-payment-form button[type="submit"]').textContent = 'Add Proposed Payment';

            // Populate targets select dropdown, restricted to this tab's type.
            const select = document.getElementById('prop-pay-target');
            select.innerHTML = '';
            state.loans.filter(card => card.type === targetType).forEach(card => {
                const opt = document.createElement('option');
                opt.value = card.id;
                opt.textContent = card.name;
                select.appendChild(opt);
            });

            document.getElementById('proposed-payment-dialog').showModal();
        });
    });

    // Cancel proposed payment dialog
    document.getElementById('btn-cancel-prop-pay').addEventListener('click', () => {
        document.getElementById('proposed-payment-dialog').close();
    });

    // Proposed Payment Submit (add or edit)
    document.getElementById('proposed-payment-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const date = document.getElementById('prop-pay-date').value;
        const source = document.getElementById('prop-pay-source').value;
        const targetId = document.getElementById('prop-pay-target').value;
        const amount = parseFloat(document.getElementById('prop-pay-amount').value);
        const isEdit = document.getElementById('prop-pay-action').value === 'edit';
        const editId = document.getElementById('prop-pay-edit-id').value;

        if (!date || !source || !targetId || isNaN(amount) || amount <= 0) return;

        const card = state.loans.find(l => l.id === targetId);
        if (!card) return;

        let linkId = 'manual-pmt-' + Math.random().toString(36).substr(2, 9);

        if (isEdit && editId) {
            // Find and remove the original checking-side entry (whichever ledger it's in), then
            // remove its card-side leg and restore that card's balance — then fall through to
            // recreate both legs fresh below. This is what makes changing the source account or
            // target card on an edit actually move the payment instead of leaving a stale original
            // and creating a duplicate.
            let oldTx = null;
            for (const list of Object.values(state.personalCalendar || {})) {
                const idx = list.findIndex(t => t.id === editId);
                if (idx > -1) { oldTx = list.splice(idx, 1)[0]; break; }
            }
            if (!oldTx) {
                const idx = state.jointRegister.findIndex(t => t.id === editId);
                if (idx > -1) oldTx = state.jointRegister.splice(idx, 1)[0];
            }
            if (!oldTx) {
                alert('Could not find the original payment to update — it may have already been deleted or modified elsewhere.');
                document.getElementById('proposed-payment-dialog').close();
                return;
            }
            if (oldTx.linkedPaymentId) linkId = oldTx.linkedPaymentId;
            removeLinkedCardPaymentLeg(oldTx);
        }

        // Subtract amount from the (possibly new) target card's current balance
        card.currentBal = Math.max(0, card.currentBal - amount);

        // Add outflow to checking calendar
        const dObj = new Date(date + 'T00:00:00');
        const y = dObj.getFullYear();
        const mShort = MONTH_ORDER[dObj.getMonth()];
        const key = `${y}-${mShort}`;

        ensureYearMonthInitialized(y, mShort);

        const checkingTxId = (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9);
        const description = `Pmt: ${card.name}`;

        if (source === 'personal') {
            state.personalCalendar[key].push({
                id: checkingTxId,
                date: date,
                description: description,
                amount: -Math.abs(amount),
                linkedPaymentId: linkId,
                payoffTargetId: targetId
            });
        } else if (source === 'joint') {
            state.jointRegister.push({
                id: checkingTxId,
                date: date,
                name: description,
                description: description,
                amount: -Math.abs(amount),
                linkedPaymentId: linkId,
                payoffTargetId: targetId
            });
        }
        
        // 3. Add inflow payment to card calendar
        if (!state.cardCalendars) state.cardCalendars = {};
        if (!state.cardCalendars[targetId]) state.cardCalendars[targetId] = {};
        if (!state.cardCalendars[targetId][key]) state.cardCalendars[targetId][key] = [];
        
        state.cardCalendars[targetId][key].push({
            id: 'c-' + Math.random().toString(36).substr(2, 9),
            date: date,
            description: `Payment from ${source === 'joint' ? 'Joint' : 'Personal'} Checking`,
            amount: Math.abs(amount),
            owner: source,
            linkedPaymentId: linkId,
            payoffTargetId: targetId
        });
        
        saveDatabase();
        renderApp();
        document.getElementById('proposed-payment-dialog').close();

        logSuccess(isEdit
            ? `Updated proposed payment: $${amount.toFixed(2)} to ${card.name} on ${date} from ${source === 'joint' ? 'Joint Checking' : 'Personal Checking'}.`
            : `Proposed payment of $${amount.toFixed(2)} to ${card.name} scheduled for ${date} from ${source === 'joint' ? 'Joint Checking' : 'Personal Checking'}!`);
    });

    // Sync form submit (mock)
    document.getElementById('sync-settings-form').addEventListener('submit', (e) => {
        e.preventDefault();
        logSystem("Saved Google Sheets sync configuration.");
        alert("Google Sheets configuration saved! Sync engine ready.");
    });

    // Test sync connection button
    document.getElementById('btn-test-connection').addEventListener('click', () => {
        logSystem("Connecting to Google Sheets API endpoint...");
        setTimeout(() => {
            logSuccess("Sheets API connection validated! Spreadsheet ID is accessible.");
        }, 1200);
    });

    // Quick add Bill Splitter item
    document.getElementById('btn-add-joint-bill').addEventListener('click', () => {
        populateCCDropdowns();
        resetBillSplitterForm();
        const ownership = state.billTrackerOwnership || 'joint';
        document.getElementById('bill-ownership').value = ownership;
        if (ownership === 'personal') document.getElementById('bill-payment-source').value = 'personalChecking';
        document.getElementById('bill-ownership').dispatchEvent(new Event('change'));
        document.getElementById('joint-bill-dialog').showModal();
    });
    document.querySelectorAll('#bill-ownership-toggle [data-bill-ownership]').forEach(button => button.addEventListener('click', () => {
        state.billTrackerOwnership = button.dataset.billOwnership;
        saveDatabase();
        renderBillsTab();
    }));
    document.getElementById('bill-ownership').addEventListener('change', () => {
        if (document.getElementById('bill-ownership').value === 'personal') {
            document.getElementById('bill-payment-source').value = 'personalChecking';
        }
        updateBillFormVisibility();
    });
    document.getElementById('bill-category-filter').addEventListener('change', renderBillsTab);
    document.querySelectorAll('[data-bills-metrics-cycle]').forEach(button => button.addEventListener('click', () => {
        state.billMetricsCycle = button.dataset.billsMetricsCycle;
        saveDatabase();
        renderBillsTab();
    }));
    document.getElementById('btn-toggle-manual-transfers').addEventListener('click', () => {
        document.getElementById('manual-transfers-list-dialog').showModal();
    });
    // Collapsible section toggles (Bill Splitter metrics, transfer calculations, and each bills
    // table) — collapsed state persists across renders/reloads via state.uiCollapsedSections since
    // renderBillsTab rebuilds the tables' contents on every render but not the static header buttons.
    if (!state.uiCollapsedSections) state.uiCollapsedSections = {};
    document.querySelectorAll('.collapse-toggle-btn').forEach(btn => {
        const key = btn.dataset.key;
        const targetEl = document.getElementById(btn.dataset.target);
        const applyState = () => {
            const collapsed = !!state.uiCollapsedSections[key];
            targetEl.classList.toggle('hidden', collapsed);
            btn.classList.toggle('collapsed', collapsed);
        };
        applyState();
        btn.addEventListener('click', () => {
            state.uiCollapsedSections[key] = !state.uiCollapsedSections[key];
            saveDatabase();
            applyState();
        });
    });
    document.getElementById('btn-close-manual-transfers-list').addEventListener('click', () => {
        document.getElementById('manual-transfers-list-dialog').close();
    });
    document.querySelectorAll('[data-bill-sort]').forEach(header => header.addEventListener('click', () => {
        const scope = state.billTrackerOwnership || 'joint';
        const current = state.billTrackerSorts[scope];
        const key = header.dataset.billSort;
        state.billTrackerSorts[scope] = { key, direction: current.key === key && current.direction === 'asc' ? 'desc' : 'asc' };
        saveDatabase();
        renderBillsTab();
    }));
    document.querySelectorAll('[data-allocation-sort]').forEach(header => header.addEventListener('click', () => {
        const current = state.billTrackerSorts.allocations;
        const key = header.dataset.allocationSort;
        state.billTrackerSorts.allocations = { key, direction: current.key === key && current.direction === 'asc' ? 'desc' : 'asc' };
        saveDatabase();
        renderBillsTab();
    }));
    document.querySelectorAll('[data-seasonal-sort]').forEach(header => header.addEventListener('click', () => {
        const current = state.billTrackerSorts.seasonal || { key: 'month', direction: 'asc' };
        const key = header.dataset.seasonalSort;
        state.billTrackerSorts.seasonal = { key, direction: current.key === key && current.direction === 'asc' ? 'desc' : 'asc' };
        saveDatabase();
        renderBillsTab();
    }));

    document.getElementById('btn-add-seasonal').addEventListener('click', () => {
        document.getElementById('seasonal-form').reset(); document.getElementById('seasonal-edit-id').value = '';
        document.getElementById('seasonal-modal-title').textContent = 'Add Seasonal Expense';
        document.getElementById('seasonal-cycles').value = '4';
        document.getElementById('seasonal-start-date').value = formatLocalDate(new Date());
        document.getElementById('seasonal-end-date').value = '';
        document.getElementById('seasonal-frequency').value = 'yearly';
        document.getElementById('seasonal-frequency-group').classList.add('hidden');
        document.getElementById('seasonal-charge-source').value = 'personal';
        document.getElementById('seasonal-charge-group').classList.add('hidden');
        document.getElementById('seasonal-dialog').showModal();
    });
    // Quick add allocation trigger
    document.getElementById('btn-add-allocation').addEventListener('click', () => {
        document.getElementById('allocation-form').reset();
        document.getElementById('alloc-edit-id').value = '';
        document.getElementById('alloc-edit-cycle').value = '';
        document.getElementById('alloc-offset-fields').classList.add('hidden');
        document.getElementById('alloc-jason-group').classList.add('hidden');
        document.getElementById('alloc-asia-group').classList.add('hidden');
        document.getElementById('alloc-recurring').checked = true;
        document.getElementById('alloc-recurrence-dates-group').classList.remove('hidden');
        document.getElementById('alloc-end-date').value = '';
        document.getElementById('alloc-frequency').value = 'monthly';
        document.getElementById('alloc-start-date').value = state.currentYear + '-' + String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0') + '-01';
        document.getElementById('alloc-frequency-preview').textContent = '1 monthly occurrence in ' + MONTH_NAMES[state.currentMonth] + '; entered amounts are applied once.';
        document.getElementById('allocation-modal-title').textContent = "Add Personal Allocation";
        document.getElementById('allocation-dialog').showModal();
    });

    // Quick add loan trigger helper
    window.openAddLoanModal = function(type) {
        document.getElementById('loan-form').reset();
        document.getElementById('loan-modal-title').textContent = type === 'credit' ? "Add Credit Card Payoff Target" : "Add Installment Loan Payoff Target";
        document.getElementById('loan-action').value = 'add';
        document.getElementById('loan-edit-id').value = '';
        
        document.getElementById('loan-type-field').value = type;
        
        // Reset promo purchase fields
        document.getElementById('loan-purchase-promo-active').checked = false;
        document.getElementById('loan-purchase-promo-fields').classList.add('hidden');
        document.getElementById('loan-purchase-promo-rate').value = '0';
        document.getElementById('loan-purchase-promo-exp').value = '';
        document.getElementById('loan-payment-strategy').value = 'none';
        document.getElementById('loan-payment-source').value = 'personal';
        
        tempEditingPromos = [];
        tempEditingPaymentPlans = [];
        resetExistingPlanEditor();
        renderEditingPaymentPlans();
        
        const isCredit = (type === 'credit');
        document.getElementById('loan-is-charge-card').checked = false;
        document.getElementById('loan-charge-card-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-limit-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-purchase-promo-section').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-payment-plans-section').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-payment-strategy-group').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-xfer-section').classList.toggle('hidden', !isCredit);
        document.getElementById('loan-statement-day-group').classList.toggle('hidden', !isCredit);
        
        // Reset mortgage fields
        document.getElementById('loan-is-mortgage').checked = false;
        document.getElementById('loan-mortgage-escrow').value = 0;
        document.getElementById('loan-mortgage-pi').value = 0;
        document.getElementById('loan-mortgage-extra').value = 0;
        document.getElementById('loan-mortgage-section').classList.toggle('hidden', isCredit);
        document.getElementById('loan-mortgage-fields').classList.add('hidden');
        
        document.getElementById('loan-dialog').showModal();
    };

    document.getElementById('btn-add-loan').addEventListener('click', () => {
        openAddLoanModal('loan');
    });

    const btnAddCC = document.getElementById('btn-add-creditcard');
    if (btnAddCC) {
        btnAddCC.addEventListener('click', () => {
            openAddLoanModal('credit');
        });
    }

    // Cancel edit transaction dialog
    document.getElementById('btn-cancel-edit-tx').addEventListener('click', () => {
        document.getElementById('edit-tx-dialog').close();
    });

    // Duplicate transaction from edit dialog
    document.getElementById('btn-duplicate-edit-tx').addEventListener('click', () => {
        const dateOrig = document.getElementById('edit-tx-date-orig').value;
        const editDate = document.getElementById('edit-tx-date').value;
        const editDesc = document.getElementById('edit-tx-desc').value;
        const duplicateCardId = state.ccSelectedCardId || (state.dashboardType !== 'personal' && state.dashboardType !== 'joint' ? state.dashboardType : '');
        if (duplicateCardId) {
            document.getElementById('edit-tx-mode').value = 'duplicate';
            document.getElementById('edit-tx-modal-title').textContent = 'Add Duplicate Transaction';
            document.getElementById('btn-save-edit-tx').textContent = 'Add Transaction';
            document.getElementById('btn-duplicate-edit-tx').classList.add('hidden');
            return;
        }
        
        if (state.ccSelectedCardId) {
            // Credit Card duplication (when inside CC sub-dashboard)
            const amountInput = parseFloat(document.getElementById('edit-tx-amount').value) || 0;
            const cardId = state.ccSelectedCardId;
            
            const dateObj = new Date(editDate + 'T00:00:00');
            const y = dateObj.getFullYear();
            const monthShort = MONTH_ORDER[dateObj.getMonth()];
            const key = `${y}-${monthShort}`;
            
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
            if (!state.cardCalendars[cardId][key]) state.cardCalendars[cardId][key] = [];
            
            state.cardCalendars[cardId][key].push({
                id: 'c-' + Math.random().toString(36).substr(2, 9),
                date: editDate,
                description: `${editDesc} (Copy)`,
                amount: -Math.abs(amountInput)
            });
            adjustCardCurrentBalance(cardId, -Math.abs(amountInput));
            logSystem(`Duplicated credit card transaction on ${editDate}: ${editDesc}`);
        } else if (state.dashboardType === 'personal') {
            const amountInput = parseFloat(document.getElementById('edit-tx-amount').value);
            if (isNaN(amountInput)) return;
            
            const dateObj = new Date(editDate + 'T00:00:00');
            const y = dateObj.getFullYear();
            const monthShort = MONTH_ORDER[dateObj.getMonth()];
            const key = `${y}-${monthShort}`;
            
            ensureYearMonthInitialized(y, monthShort);
            if (!state.personalCalendar[key]) state.personalCalendar[key] = [];
            
            state.personalCalendar[key].push({
                id: 'p-' + Math.random().toString(36).substr(2, 9),
                date: editDate,
                description: `${editDesc} (Copy)`,
                amount: amountInput
            });
            
            logSystem(`Duplicated personal transaction on ${editDate}: ${editDesc}`);
        } else if (state.dashboardType === 'joint') {
            // Joint transaction duplication
            const id = document.getElementById('edit-tx-id').value;
            const origTx = state.jointRegister.find(t => t.id === id);
            
            if (origTx) {
                if (origTx.type === 'contribution') {
                    const jasonAmt = parseFloat(document.getElementById('edit-tx-jason').value) || 0;
                    const asiaAmt = parseFloat(document.getElementById('edit-tx-asia').value) || 0;
                    const totalAmt = jasonAmt + asiaAmt;
                    
                    state.jointRegister.push({
                        id: 'j-' + Math.random().toString(36).substr(2, 9),
                        type: 'contribution',
                        name: `${editDesc} (Copy)`,
                        jason: jasonAmt,
                        asia: asiaAmt,
                        amount: totalAmt,
                        date: editDate
                    });
                } else {
                    const amountInput = parseFloat(document.getElementById('edit-tx-amount').value) || 0;
                    state.jointRegister.push({
                        id: 'j-' + Math.random().toString(36).substr(2, 9),
                        type: 'expense',
                        name: `${editDesc} (Copy)`,
                        amount: -Math.abs(amountInput),
                        date: editDate
                    });
                }
                logSystem(`Duplicated joint transaction on ${editDate}: ${editDesc}`);
            }
        } else {
            // Credit Card duplication (fallback if somehow dashboardType is cardId)
            const amountInput = parseFloat(document.getElementById('edit-tx-amount').value) || 0;
            const cardId = state.dashboardType;
            
            const dateObj = new Date(editDate + 'T00:00:00');
            const y = dateObj.getFullYear();
            const monthShort = MONTH_ORDER[dateObj.getMonth()];
            const key = `${y}-${monthShort}`;
            
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
            if (!state.cardCalendars[cardId][key]) state.cardCalendars[cardId][key] = [];
            
            state.cardCalendars[cardId][key].push({
                id: 'c-' + Math.random().toString(36).substr(2, 9),
                date: editDate,
                description: `${editDesc} (Copy)`,
                amount: -Math.abs(amountInput)
            });
            adjustCardCurrentBalance(cardId, -Math.abs(amountInput));
            logSystem(`Duplicated credit card transaction on ${editDate}: ${editDesc}`);
        }
        
        saveDatabase();
        document.getElementById('edit-tx-dialog').close();
        renderApp();
    });

    // Delete transaction from edit dialog
    document.getElementById('btn-delete-edit-tx').addEventListener('click', () => {
        const id = document.getElementById('edit-tx-id').value;
        const dateOrig = document.getElementById('edit-tx-date-orig').value;
        const editMode = document.getElementById('edit-tx-mode').value;

        // Handle dynamic transaction override delete
        if (editMode === 'dynamic-override') {
            const settingLabel = id.startsWith('dynamic-paycheck-') ? 'payroll schedule' : 'bill splitter settings';
            if (confirm(`Are you sure you want to hide this dynamic transaction? This does not change your ${settingLabel}.`)) {
                saveDynamicTxOverride(id, { deleted: true });
                saveDatabase();
                document.getElementById('edit-tx-dialog').close();
                renderApp();
                logSystem(`Hidden dynamic transaction ${id}`);
            }
            return;
        }

        let removed = null;
        let cardIdUsed = '';
        
        if (state.ccSelectedCardId) {
            const cardId = state.ccSelectedCardId;
            cardIdUsed = cardId;
            const dateObj = new Date(dateOrig + 'T00:00:00');
            const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
            const list = (state.cardCalendars && state.cardCalendars[cardId]) ? (state.cardCalendars[cardId][key] || []) : [];
            const idx = list.findIndex(tx => tx.id === id);
            if (idx > -1) {
                removed = deleteCardTransactionWithRecurringChoice(cardId, key, id);
                if (!removed) return;
                // Adjust currentBal: if charge (negative), decrease balance; if payment (positive), increase balance
                const cardObj = state.loans.find(l => l.id === cardId);
                if (cardObj) {
                    if (removed.amount < 0) {
                        cardObj.currentBal = Math.max(0, cardObj.currentBal - Math.abs(removed.amount));
                    } else {
                        cardObj.currentBal += removed.amount;
                    }
                }
                logSystem(`Deleted credit card transaction: ${removed.description} (-$${Math.abs(removed.amount).toFixed(2)})`);
            }
        } else if (state.dashboardType === 'personal') {
            const dateObj = new Date(dateOrig + 'T00:00:00');
            const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
            const list = state.personalCalendar[key] || [];
            const idx = list.findIndex(tx => tx.id === id);
            if (idx > -1) {
                const tx = list[idx];
                if (tx.isAutomaticCardPayment) {
                    alert('Automatic card payments cannot be deleted from the ledger. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
                    return;
                }
                if (tx.linkedBillId) {
                    // Bill-generated occurrence: flag instead of splicing, or the sync regenerates it.
                    tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date;
                    tx.billOccurrenceDeleted = true;
                    removed = tx;
                    logSystem(`Deleted bill occurrence: ${tx.description} on ${tx.date} (bill setting unchanged)`);
                } else {
                    removed = list.splice(idx, 1)[0];
                    removeCheckingTransferMirror(removed, 'personal');
                    logSystem(`Deleted personal transaction: ${removed.description} ($${removed.amount.toFixed(2)})`);
                }
            }
        } else if (state.dashboardType === 'joint') {
            const idx = state.jointRegister.findIndex(tx => tx.id === id);
            if (idx > -1) {
                const jointTx = state.jointRegister[idx];
                if (jointTx.isAutomaticCardPayment) {
                    alert('Automatic card payments cannot be deleted from the ledger. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
                    return;
                }
                if (jointTx.linkedBillId) {
                    // Bill-generated occurrence: flag instead of splicing, or the sync regenerates it.
                    jointTx.billOccurrenceDate = jointTx.billOccurrenceDate || jointTx.date;
                    jointTx.billOccurrenceDeleted = true;
                    removed = { ...jointTx, description: jointTx.description || jointTx.name };
                    logSystem(`Deleted bill occurrence: ${removed.description} on ${jointTx.date} (bill setting unchanged)`);
                } else {
                    const removedTx = state.jointRegister.splice(idx, 1)[0];
                    removed = { ...removedTx, description: removedTx.description || removedTx.name };
                    removeCheckingTransferMirror(removedTx, 'joint');
                    logSystem(`Deleted joint transaction: ${removed.description} ($${Math.abs(removed.amount).toFixed(2)})`);
                }
            }
        } else {
            const cardId = state.dashboardType;
            cardIdUsed = cardId;
            const dateObj = new Date(dateOrig + 'T00:00:00');
            const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
            const list = (state.cardCalendars && state.cardCalendars[cardId]) ? (state.cardCalendars[cardId][key] || []) : [];
            const idx = list.findIndex(tx => tx.id === id);
            if (idx > -1) {
                removed = deleteCardTransactionWithRecurringChoice(cardId, key, id);
                if (!removed) return;
                // Adjust currentBal
                const cardObj = state.loans.find(l => l.id === cardId);
                if (cardObj) {
                    if (removed.amount < 0) {
                        cardObj.currentBal = Math.max(0, cardObj.currentBal - Math.abs(removed.amount));
                    } else {
                        cardObj.currentBal += removed.amount;
                    }
                }
                logSystem(`Deleted credit card transaction: ${removed.description} (-$${Math.abs(removed.amount).toFixed(2)})`);
            }
        }
        
        // Synced payment cleanup logic
        if (removed) {
            if (removed.linkedPaymentId) {
                // Remove checking side transaction
                Object.values(state.personalCalendar || {}).forEach(list => {
                    const idx = list.findIndex(tx => tx.linkedPaymentId === removed.linkedPaymentId);
                    if (idx > -1) list.splice(idx, 1);
                });
                const jIdx = state.jointRegister.findIndex(tx => tx.linkedPaymentId === removed.linkedPaymentId);
                if (jIdx > -1) state.jointRegister.splice(jIdx, 1);

                // Remove card side transaction & restore balance
                Object.keys(state.cardCalendars || {}).forEach(cId => {
                    Object.values(state.cardCalendars[cId] || {}).forEach(list => {
                        const idx = list.findIndex(tx => tx.linkedPaymentId === removed.linkedPaymentId);
                        if (idx > -1) {
                            const cRemoved = list.splice(idx, 1)[0];
                            const cardObj = state.loans.find(l => l.id === cId);
                            if (cardObj) {
                                cardObj.currentBal = Math.max(0, cardObj.currentBal + Math.abs(cRemoved.amount));
                            }
                        }
                    });
                });
                logSystem(`Synced: Deleted corresponding checking/card payment log.`);
            } else {
                const amt = Math.abs(removed.amount);
                // Fallback to legacy description/amt matching if no linkedPaymentId
                if (removed.description && removed.description.startsWith('Pmt: ')) {
                    const cardName = removed.description.replace('Pmt: ', '');
                    const cardObj = state.loans.find(l => l.name === cardName);
                    if (cardObj) {
                        cardObj.currentBal += amt;
                        const dObj = new Date(removed.date + 'T00:00:00');
                        const cKey = `${dObj.getFullYear()}-${MONTH_ORDER[dObj.getMonth()]}`;
                        if (state.cardCalendars && state.cardCalendars[cardObj.id] && state.cardCalendars[cardObj.id][cKey]) {
                            const ccList = state.cardCalendars[cardObj.id][cKey];
                            const ccIdx = ccList.findIndex(tx => tx.date === removed.date && Math.abs(tx.amount - amt) < 0.01 && tx.description.startsWith('Payment from'));
                            if (ccIdx > -1) {
                                ccList.splice(ccIdx, 1);
                            }
                        }
                    }
                } else if (removed.description && removed.description.startsWith('Payment from ') && cardIdUsed) {
                    const checkingType = removed.description.includes('Joint') ? 'joint' : 'personal';
                    const cardObj = state.loans.find(l => l.id === cardIdUsed);
                    if (cardObj) {
                        cardObj.currentBal += amt;
                    }
                    if (checkingType === 'personal') {
                        const dObj = new Date(removed.date + 'T00:00:00');
                        const cKey = `${dObj.getFullYear()}-${MONTH_ORDER[dObj.getMonth()]}`;
                        if (state.personalCalendar && state.personalCalendar[cKey]) {
                            const pList = state.personalCalendar[cKey];
                            const pIdx = pList.findIndex(tx => tx.date === removed.date && Math.abs(Math.abs(tx.amount) - amt) < 0.01 && tx.description.startsWith('Pmt: '));
                            if (pIdx > -1) {
                                pList.splice(pIdx, 1);
                            }
                        }
                    } else if (checkingType === 'joint') {
                        if (state.jointRegister) {
                            const jIdx = state.jointRegister.findIndex(tx => tx.date === removed.date && Math.abs(Math.abs(tx.amount) - amt) < 0.01 && tx.description.startsWith('Pmt: '));
                            if (jIdx > -1) {
                                state.jointRegister.splice(jIdx, 1);
                            }
                        }
                    }
                }
            }
        }
        
        saveDatabase();
        document.getElementById('edit-tx-dialog').close();
        renderApp();
    });

    // Submit edit transaction dialog
    document.getElementById('edit-tx-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const id = document.getElementById('edit-tx-id').value;
        const dateOrig = document.getElementById('edit-tx-date-orig').value;
        const editMode = document.getElementById('edit-tx-mode').value;

        // Handle dynamic transaction override save
        if (editMode === 'dynamic-override') {
            const newDesc = document.getElementById('edit-tx-desc').value.trim();
            const newAmt = parseFloat(document.getElementById('edit-tx-amount').value);
            // Preserve sign: personal transfers are outflows; joint contributions are inflows.
            const isOutflow = id.startsWith('xfer-');
            saveDynamicTxOverride(id, {
                description: newDesc || undefined,
                amount: isOutflow ? -Math.abs(newAmt) : Math.abs(newAmt),
                deleted: false
            });
            saveDatabase();
            document.getElementById('edit-tx-dialog').close();
            renderApp();
            logSuccess(`Updated dynamic transaction override for ${id}`);
            return;
        }
        const newDate = document.getElementById('edit-tx-date').value;
        const newDesc = document.getElementById('edit-tx-desc').value;
        const newMerchant = document.getElementById('edit-tx-merchant').value.trim();
        const newKind = document.getElementById('edit-tx-kind').value;
        const newOwner = document.getElementById('edit-tx-owner').value;
        const newTrip = document.getElementById('edit-tx-trip').value.trim();
        const isRecurring = document.getElementById('edit-tx-recurring').checked;
        const recurringDay = parseInt(document.getElementById('edit-tx-recurring-day').value) || 0;
        const recurringEnabled = newKind === 'charge' && isRecurring;
        const duplicateCardId = state.ccSelectedCardId || (state.dashboardType !== 'personal' && state.dashboardType !== 'joint' ? state.dashboardType : '');

        if (editMode === 'duplicate' && duplicateCardId) {
            const duplicateAmount = parseFloat(document.getElementById('edit-tx-amount').value);
            if (!newDate || !newDesc || !Number.isFinite(duplicateAmount)) return;
            const dateObj = new Date(newDate + 'T00:00:00');
            const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
            if (!state.cardCalendars[duplicateCardId]) state.cardCalendars[duplicateCardId] = {};
            if (!state.cardCalendars[duplicateCardId][key]) state.cardCalendars[duplicateCardId][key] = [];
            const signedAmount = newKind === 'charge' ? -Math.abs(duplicateAmount) : Math.abs(duplicateAmount);
            const duplicateTx = {
                id: 'c-' + Math.random().toString(36).substr(2, 9),
                date: newDate,
                merchant: newMerchant,
                description: newDesc,
                amount: signedAmount,
                transactionKind: newKind,
                owner: newOwner,
                trip: newTrip,
                isRecurring: recurringEnabled,
                recurringDay: recurringEnabled ? recurringDay : 0,
                recurringSeriesId: recurringEnabled ? 'series-' + Math.random().toString(36).substr(2, 9) : ''
            };
            state.cardCalendars[duplicateCardId][key].push(duplicateTx);
            adjustCardCurrentBalance(duplicateCardId, signedAmount);
            updateTransactionPaymentPlan(duplicateCardId, duplicateTx, newKind === 'charge' && document.getElementById('edit-tx-payment-plan').checked);
            saveDatabase();
            document.getElementById('edit-tx-dialog').close();
            renderApp();
            logSuccess(`Added duplicated ${newKind}: ${newDesc} ($${Math.abs(duplicateAmount).toFixed(2)}).`);
            return;
        }
        
        if (state.ccSelectedCardId) {
            const newAmt = parseFloat(document.getElementById('edit-tx-amount').value);
            if (isNaN(newAmt)) return;
            
            const cardId = state.ccSelectedCardId;
            const origDateObj = new Date(dateOrig + 'T00:00:00');
            const origKey = `${origDateObj.getFullYear()}-${MONTH_ORDER[origDateObj.getMonth()]}`;
            const targetDateObj = new Date(newDate + 'T00:00:00');
            const targetKey = `${targetDateObj.getFullYear()}-${MONTH_ORDER[targetDateObj.getMonth()]}`;
            
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
            
            const list = state.cardCalendars[cardId][origKey] || [];
            const tx = list.find(t => t.id === id);
            if (tx) {
                if (tx.linkedBillId) { tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date; tx.billOccurrenceOverridden = true; }
                // Adjust currentBal for amount delta
                const oldAmt = tx.amount;
                const newAmtSigned = newKind === 'charge' ? -Math.abs(newAmt) : Math.abs(newAmt);
                const cardObj = state.loans.find(l => l.id === cardId);
                if (cardObj) {
                    // Reverse old amount effect, apply new
                    if (oldAmt < 0) cardObj.currentBal -= Math.abs(oldAmt);
                    else cardObj.currentBal += oldAmt;
                    if (newAmtSigned < 0) cardObj.currentBal += Math.abs(newAmtSigned);
                    else cardObj.currentBal -= newAmtSigned;
                    cardObj.currentBal = Math.max(0, cardObj.currentBal);
                }
                
                tx.date = newDate;
                tx.description = newDesc;
                tx.merchant = newMerchant;
                tx.transactionKind = newKind;
                tx.owner = newOwner;
                tx.trip = newTrip;
                tx.amount = newAmtSigned;
                if (tx.isAutomaticCardPayment) {
                    tx.automaticPaymentOverridden = true;
                    tx.transactionKind = 'payment';
                    tx.amount = Math.abs(newAmt);
                    syncAutomaticCardPaymentOverride(tx, cardId);
                }
                if (tx.linkedBillId) {
                    tx.isRecurring = true;
                } else {
                    tx.isRecurring = recurringEnabled;
                    tx.recurringDay = recurringEnabled ? recurringDay : 0;
                    if (recurringEnabled) propagateRecurringChargeChanges(cardId, tx);
                }
                updateTransactionPaymentPlan(cardId, tx, newKind === 'charge' && document.getElementById('edit-tx-payment-plan').checked);
                syncLinkedPayoffPayment(tx);
                
                if (origKey !== targetKey) {
                    const idx = list.indexOf(tx);
                    list.splice(idx, 1);
                    if (!state.cardCalendars[cardId][targetKey]) state.cardCalendars[cardId][targetKey] = [];
                    state.cardCalendars[cardId][targetKey].push(tx);
                }
                logSystem(`Updated credit card transaction: ${newDesc} (-$${Math.abs(newAmt).toFixed(2)})`);
            }
        } else if (state.dashboardType === 'personal') {
            const newAmt = parseFloat(document.getElementById('edit-tx-amount').value);
            if (isNaN(newAmt)) return;
            
            const origDateObj = new Date(dateOrig + 'T00:00:00');
            const origKey = `${origDateObj.getFullYear()}-${MONTH_ORDER[origDateObj.getMonth()]}`;
            const targetDateObj = new Date(newDate + 'T00:00:00');
            const targetKey = `${targetDateObj.getFullYear()}-${MONTH_ORDER[targetDateObj.getMonth()]}`;
            
            const list = state.personalCalendar[origKey] || [];
            const tx = list.find(t => t.id === id);
            if (tx && tx.isAutomaticCardPayment) {
                // Amount-only override: date/description are locked in the dialog; the override is
                // mirrored onto the card-side leg and flagged so the auto-payment regeneration
                // preserves it. Neither the Bill Splitter budget nor the strategy is touched.
                tx.amount = -Math.abs(newAmt);
                tx.automaticPaymentOverridden = true;
                const cardLeg = findAutomaticCardLeg(tx.automaticPaymentId);
                if (cardLeg) { cardLeg.amount = Math.abs(newAmt); cardLeg.automaticPaymentOverridden = true; }
                logSystem(`Overrode automatic payment amount: ${tx.description} → $${Math.abs(newAmt).toFixed(2)}`);
            } else if (tx) {
                if (tx.linkedBillId) { tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date; tx.billOccurrenceOverridden = true; }
                tx.date = newDate;
                tx.description = newDesc;
                tx.amount = newAmt;
                syncCheckingTransferMirror(tx, 'personal');
                syncCheckingPaymentToCard(tx);
                
                if (origKey !== targetKey) {
                    const idx = list.indexOf(tx);
                    list.splice(idx, 1);
                    ensureYearMonthInitialized(targetDateObj.getFullYear(), MONTH_ORDER[targetDateObj.getMonth()]);
                    if (!state.personalCalendar[targetKey]) state.personalCalendar[targetKey] = [];
                    state.personalCalendar[targetKey].push(tx);
                }
                logSystem(`Updated personal transaction: ${newDesc} ($${newAmt.toFixed(2)})`);
            }
        } else if (state.dashboardType === 'joint') {
            const tx = state.jointRegister.find(t => t.id === id);
            if (tx && tx.isAutomaticCardPayment) {
                // Amount-only override; see the personal branch above for the rationale.
                const overrideAmt = parseFloat(document.getElementById('edit-tx-amount').value);
                if (!isNaN(overrideAmt)) {
                    tx.amount = -Math.abs(overrideAmt);
                    tx.automaticPaymentOverridden = true;
                    const cardLeg = findAutomaticCardLeg(tx.automaticPaymentId);
                    if (cardLeg) { cardLeg.amount = Math.abs(overrideAmt); cardLeg.automaticPaymentOverridden = true; }
                    logSystem(`Overrode automatic payment amount: ${tx.name} → $${Math.abs(overrideAmt).toFixed(2)}`);
                }
            } else if (tx) {
                if (tx.linkedBillId) { tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date; tx.billOccurrenceOverridden = true; }
                tx.date = newDate;
                tx.name = newDesc;
                
                if (tx.type === 'contribution') {
                    const jasonAmt = parseFloat(document.getElementById('edit-tx-jason').value) || 0;
                    const asiaAmt = parseFloat(document.getElementById('edit-tx-asia').value) || 0;
                    tx.jason = jasonAmt;
                    tx.asia = asiaAmt;
                    tx.amount = jasonAmt + asiaAmt;
                    if (jasonAmt !== 0 && !tx.transferId) tx.transferId = 'checking-xfer-' + Math.random().toString(36).substr(2, 9);
                    if (jasonAmt === 0 && tx.transferId) {
                        removeCheckingTransferMirror(tx, 'joint');
                        tx.transferId = '';
                    }
                } else {
                    const newAmt = parseFloat(document.getElementById('edit-tx-amount').value);
                    if (!isNaN(newAmt)) {
                        tx.amount = -Math.abs(newAmt);
                    }
                }
                syncCheckingTransferMirror(tx, 'joint');
                syncCheckingPaymentToCard(tx);
                logSystem(`Updated joint transaction: ${newDesc}`);
            }
        } else {
            // Credit Card fallback
            const newAmt = parseFloat(document.getElementById('edit-tx-amount').value);
            if (isNaN(newAmt)) return;
            
            const cardId = state.dashboardType;
            const origDateObj = new Date(dateOrig + 'T00:00:00');
            const origKey = `${origDateObj.getFullYear()}-${MONTH_ORDER[origDateObj.getMonth()]}`;
            const targetDateObj = new Date(newDate + 'T00:00:00');
            const targetKey = `${targetDateObj.getFullYear()}-${MONTH_ORDER[targetDateObj.getMonth()]}`;
            
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
            
            const list = state.cardCalendars[cardId][origKey] || [];
            const tx = list.find(t => t.id === id);
            if (tx) {
                if (tx.linkedBillId) { tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date; tx.billOccurrenceOverridden = true; }
                // Adjust currentBal for amount delta
                const oldAmt = tx.amount;
                const newAmtSigned = newKind === 'charge' ? -Math.abs(newAmt) : Math.abs(newAmt);
                const cardObj = state.loans.find(l => l.id === cardId);
                if (cardObj) {
                    if (oldAmt < 0) cardObj.currentBal -= Math.abs(oldAmt);
                    else cardObj.currentBal += oldAmt;
                    if (newAmtSigned < 0) cardObj.currentBal += Math.abs(newAmtSigned);
                    else cardObj.currentBal -= newAmtSigned;
                    cardObj.currentBal = Math.max(0, cardObj.currentBal);
                }
                
                tx.date = newDate;
                tx.description = newDesc;
                tx.merchant = newMerchant;
                tx.transactionKind = newKind;
                tx.owner = newOwner;
                tx.trip = newTrip;
                tx.amount = newAmtSigned;
                if (tx.isAutomaticCardPayment) {
                    tx.automaticPaymentOverridden = true;
                    tx.transactionKind = 'payment';
                    tx.amount = Math.abs(newAmt);
                    syncAutomaticCardPaymentOverride(tx, cardId);
                }
                if (tx.linkedBillId) {
                    tx.isRecurring = true;
                } else {
                    tx.isRecurring = recurringEnabled;
                    tx.recurringDay = recurringEnabled ? recurringDay : 0;
                    if (recurringEnabled) propagateRecurringChargeChanges(cardId, tx);
                }
                updateTransactionPaymentPlan(cardId, tx, newKind === 'charge' && document.getElementById('edit-tx-payment-plan').checked);
                syncLinkedPayoffPayment(tx);
                
                if (origKey !== targetKey) {
                    const idx = list.indexOf(tx);
                    list.splice(idx, 1);
                    if (!state.cardCalendars[cardId][targetKey]) state.cardCalendars[cardId][targetKey] = [];
                    state.cardCalendars[cardId][targetKey].push(tx);
                }
                logSystem(`Updated credit card transaction: ${newDesc} (-$${Math.abs(newAmt).toFixed(2)})`);
            }
        }
        
        saveDatabase();
        document.getElementById('edit-tx-dialog').close();
        renderApp();
    });

    // Global layout expansion maximize listener
    document.getElementById('btn-toggle-layout-maximize').addEventListener('click', () => {
        const isMaximized = document.body.classList.toggle('maximized-calendar');
        const btn = document.getElementById('btn-toggle-layout-maximize');
        if (btn) {
            if (isMaximized) {
                btn.textContent = '⤡ Collapse';
                btn.title = 'Restore standard layout';
            } else {
                btn.textContent = '⤢ Expand View';
                btn.title = 'Toggle full-screen view';
            }
        }
        renderApp();
    });

    // Metrics visibility toggle listener
    document.getElementById('btn-toggle-metrics').addEventListener('click', () => {
        state.metricsCollapsed = !state.metricsCollapsed;
        saveDatabase();
        renderApp();
    });

        // ⚙️ Payroll button handler
    const btnConfigurePayroll = document.getElementById('btn-configure-payroll');
    if (btnConfigurePayroll) {
        btnConfigurePayroll.addEventListener('click', () => {
            const config = state.payrollConfig;
            document.getElementById('payroll-base-pay').value = config.baseNetPay || 0;
            document.getElementById('payroll-stipend').value = config.stipendAmount || 0;
            document.getElementById('payroll-first-date').value = config.firstPayDate || '2026-01-02';
            
            // Custom check rates check
            const hasCustom = !!config.hasDifferentRates;
            document.getElementById('payroll-custom-rates-toggle').checked = hasCustom;
            document.getElementById('payroll-custom-rates-panel').classList.toggle('hidden', !hasCustom);
            document.getElementById('payroll-rate-1st').value = config.differentRates?.rate1st || 0;
            document.getElementById('payroll-rate-2nd').value = config.differentRates?.rate2nd || 0;
            document.getElementById('payroll-rate-3rd').value = config.differentRates?.rate3rd || 0;
            
            // Render estimates list
            renderPayrollEstimatesList();
            
            document.getElementById('payroll-config-dialog').showModal();
        });
    }

    // Toggle custom rates panel when checkbox changes
    document.getElementById('payroll-custom-rates-toggle').addEventListener('change', (e) => {
        document.getElementById('payroll-custom-rates-panel').classList.toggle('hidden', !e.target.checked);
    });

    // Close payroll configuration dialog
    document.getElementById('btn-cancel-payroll').addEventListener('click', () => {
        document.getElementById('payroll-config-dialog').close();
    });

    // Close payroll configuration dialog with cross button
    const btnClosePayroll = document.getElementById('btn-close-payroll');
    if (btnClosePayroll) {
        btnClosePayroll.addEventListener('click', () => {
            document.getElementById('payroll-config-dialog').close();
        });
    }

    // Add payroll estimate trigger
    const btnAddPayrollEst = document.getElementById('btn-add-payroll-est');
    if (btnAddPayrollEst) {
        btnAddPayrollEst.addEventListener('click', () => {
            const month = document.getElementById('payroll-est-month').value;
            const year = parseInt(document.getElementById('payroll-est-year').value);
            const type = document.getElementById('payroll-est-type').value;
            const val = parseFloat(document.getElementById('payroll-est-val').value);
            
            if (!month || isNaN(year) || isNaN(val) || val <= 0) {
                alert('Please enter valid raise estimate fields.');
                return;
            }
            
            state.payrollConfig.estimates = state.payrollConfig.estimates || [];
            state.payrollConfig.estimates.push({
                id: 'est-' + Math.random().toString(36).substr(2, 9),
                effectiveMonth: month,
                effectiveYear: year,
                type: type,
                value: val,
                isRecurring: document.getElementById('payroll-est-recur').checked
            });
            
            // Reset inputs
            document.getElementById('payroll-est-val').value = '';
            document.getElementById('payroll-est-recur').checked = false;
            
            renderPayrollEstimatesList();
        });
    }

    // Save payroll configuration submit
    document.getElementById('payroll-config-form').addEventListener('submit', (e) => {
        e.preventDefault();
        
        const baseRate = parseFloat(document.getElementById('payroll-base-pay').value) || 0;
        const baseRateStipend = parseFloat(document.getElementById('payroll-stipend').value) || 0;
        const firstPaycheckDate = document.getElementById('payroll-first-date').value;
        const useCustomRates = document.getElementById('payroll-custom-rates-toggle').checked;
        const rate1st = parseFloat(document.getElementById('payroll-rate-1st').value) || 0;
        const rate2nd = parseFloat(document.getElementById('payroll-rate-2nd').value) || 0;
        const rate3rd = parseFloat(document.getElementById('payroll-rate-3rd').value) || 0;
        
        state.payrollConfig.baseNetPay = baseRate;
        state.payrollConfig.stipendAmount = baseRateStipend;
        state.payrollConfig.firstPayDate = firstPaycheckDate;
        state.payrollConfig.hasDifferentRates = useCustomRates;
        state.payrollConfig.differentRates = {
            rate1st: rate1st,
            rate2nd: rate2nd,
            rate3rd: rate3rd
        };
        
        saveDatabase();
        document.getElementById('payroll-config-dialog').close();
        renderApp();
        logSuccess('Payroll configuration saved successfully!');
    });

    // Segmented cycle filter clicks
    document.querySelectorAll('#cycle-filter-container .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            document.querySelectorAll('#cycle-filter-container .segment-btn').forEach(b => b.classList.remove('active'));
            e.currentTarget.classList.add('active');
            state.listCycleFilter = e.currentTarget.dataset.cycle;
            renderApp();
        });
    });
}

function populateCheckingAutocomplete() {
    const personalDescs = Object.values(state.personalCalendar || {})
        .flatMap(list => list || [])
        .map(tx => String(tx.description || '').trim());
        
    const jointDescs = (state.jointRegister || [])
        .map(tx => String(tx.description || '').trim());
        
    const seen = new Set();
    const uniqueDescs = [];
    [...personalDescs, ...jointDescs].forEach(desc => {
        const val = desc.trim();
        const normalized = val.toLowerCase();
        if (val && !seen.has(normalized)) {
            seen.add(normalized);
            uniqueDescs.push(val);
        }
    });
    
    uniqueDescs.sort((a, b) => a.localeCompare(b));
    
    const list = document.getElementById('checking-description-suggestions');
    if (list) {
        list.replaceChildren();
        uniqueDescs.slice(0, 100).forEach(value => {
            const option = document.createElement('option');
            option.value = value;
            list.appendChild(option);
        });
    }
}

// --- RENDERING ROUTINES ---
// Public entry point: shows a busy spinner, yields to the browser so it actually paints before the
// (synchronous, potentially slow) render runs, then renders and hides the spinner. Deferred by a
// couple of animation frames rather than calling renderAppImmediate() directly — without that yield,
// the spinner would never actually appear on screen, since the browser can't paint in the middle of a
// blocking synchronous call.
function renderApp() {
    const overlay = document.getElementById('app-busy-overlay');
    if (overlay) overlay.classList.remove('hidden');
    requestAnimationFrame(() => {
        requestAnimationFrame(() => {
            // If renderAppImmediate() throws partway through, the overlay must still come down —
            // otherwise a single error leaves the whole app looking permanently stuck "loading" with no
            // visible indication anything went wrong, instead of surfacing the broken UI underneath.
            try {
                renderAppImmediate();
            } finally {
                if (overlay) overlay.classList.add('hidden');
            }
            queuePrewarmForCurrentMonth();
        });
    });
}

// Warms the balance/transfer caches for the months around the current one (both forward and back) in
// the background so navigating either direction feels instant instead of paying the first-visit cost
// at click time. Uses a plain setTimeout chain
// rather than requestIdleCallback — idle callbacks get starved/throttled in backgrounded or
// non-foreground tabs (common when the app is embedded, e.g. in a Google Sites iframe) and can stall
// indefinitely, whereas setTimeout keeps making steady, predictable progress.
//
// renderApp() and saveDatabase() both fire many times in quick succession during page init and during
// any multi-step edit, and each one invalidates the currently-visible month's caches. Restarting the
// prewarm chain immediately on every one of those calls means it never gets past the first step or two
// before being reset again. queuePrewarmForCurrentMonth() debounces that: only the render that settles
// (no further renderApp() for _PREWARM_DEBOUNCE_MS) actually kicks off a prewarm chain. The
// _prewarmGeneration check inside the chain is a second line of defense for the rare case a real edit
// lands mid-chain.
let _prewarmGeneration = 0;
let _prewarmDebounceTimer = null;
const _PREWARM_DEBOUNCE_MS = 300;
const _PREWARM_STEP_MS = 40;
const _requestIdle = (cb) => setTimeout(cb, _PREWARM_STEP_MS);

function queuePrewarmForCurrentMonth() {
    clearTimeout(_prewarmDebounceTimer);
    _prewarmDebounceTimer = setTimeout(() => {
        scheduleMonthPrewarm(state.currentYear, state.currentMonth);
    }, _PREWARM_DEBOUNCE_MS);
}

// Offsets to prewarm around the current month, nearest-first and alternating direction (so a single
// step back or forward is warmed almost immediately either way), then continuing forward out to
// _PREWARM_FORWARD_MONTHS once the near-backward range is exhausted, since forward is the far more
// common browsing direction once you land somewhere new.
const _PREWARM_FORWARD_MONTHS = 24;
const _PREWARM_BACKWARD_MONTHS = 6;
function _buildPrewarmOffsets() {
    const offsets = [];
    const both = Math.min(_PREWARM_FORWARD_MONTHS, _PREWARM_BACKWARD_MONTHS);
    for (let i = 1; i <= both; i++) { offsets.push(i); offsets.push(-i); }
    for (let i = both + 1; i <= _PREWARM_FORWARD_MONTHS; i++) offsets.push(i);
    for (let i = both + 1; i <= _PREWARM_BACKWARD_MONTHS; i++) offsets.push(-i);
    return offsets;
}
const _PREWARM_OFFSETS = _buildPrewarmOffsets();

function scheduleMonthPrewarm(year, monthShort) {
    const myGeneration = ++_prewarmGeneration;
    let stepIndex = 0;

    function step() {
        if (myGeneration !== _prewarmGeneration) return; // superseded by a newer navigation/edit
        if (stepIndex >= _PREWARM_OFFSETS.length) return;
        const offset = _PREWARM_OFFSETS[stepIndex];
        stepIndex++;

        const startIdx = MONTH_ORDER.indexOf(monthShort);
        const globalIdx = startIdx + offset;
        const y = year + Math.floor(globalIdx / 12);
        const mStr = MONTH_ORDER[((globalIdx % 12) + 12) % 12];
        const mm = String(MONTH_ORDER.indexOf(mStr) + 1).padStart(2, '0');

        try {
            getSimulatedTransferAdjustmentsForMonth(y, mStr, buildCalendarGridDates(y, mStr));
            getJointRunningBalanceAtDate(`${y}-${mm}-01`);
            getJointRunningBalanceAtDate(`${y}-${mm}-15`);
        } catch (e) { /* never let a background prewarm surface an error to the user */ }

        _requestIdle(step);
    }

    _requestIdle(step);
}

// Calendar grids are unreadable at phone width, so on mobile we force every calendar/list toggle
// (personal/joint dashboard, credit cards, savings) to list mode. Matches the CSS breakpoint that
// hides the calendar containers and the "Calendar" toggle buttons (see index.css @media 900px), and
// reuses the same isMobileViewport() the sidebar/resize logic already defines.
function enforceMobileListView() {
    if (!isMobileViewport()) return;
    state.viewMode = 'list';
    state.ccViewMode = 'list';
    state.savingsViewMode = 'list';
    // The metrics-collapsed state persists from whatever it was last set to (often on desktop), and
    // .metrics-collapsed fully hides the summary cards — on a phone that reads as "metrics missing"
    // rather than "collapsed," so always show them by default on mobile.
    state.metricsCollapsed = false;
}

function renderAppImmediate() {
    enforceMobileListView();
    populateCheckingAutocomplete();
    populateCCDropdowns();
    renderSummaryCards();
    
    const activeTab = document.querySelector('.nav-btn.active').dataset.tab;
    const metricsCollapsed = !!state.metricsCollapsed;
    const summaryCards = document.getElementById('summary-cards');
    const isLoans = activeTab === 'loans';
    const isCC = activeTab === 'creditcards';
    const isBillTracker = activeTab === 'billtracker';
    const hideGlobalSummary = isLoans || isCC || isBillTracker || activeTab === 'bills' || activeTab === 'savings';
    
    // Bill Splitter has its own dedicated metrics; hide the global dashboard there.
    summaryCards.classList.toggle('hidden', hideGlobalSummary);
    
    if (!hideGlobalSummary) {
        summaryCards.classList.toggle('metrics-collapsed', metricsCollapsed);
    } else {
        summaryCards.classList.remove('metrics-collapsed');
    }
    
    const btnToggleMetrics = document.getElementById('btn-toggle-metrics');
    if (btnToggleMetrics) {
        btnToggleMetrics.innerHTML = metricsCollapsed ? '📊 Show Metrics' : '📊 Hide Metrics';
        btnToggleMetrics.classList.toggle('hidden', isLoans || isCC || isBillTracker || activeTab === 'sync' || activeTab === 'bills' || activeTab === 'savings');
    }
    
    const btnMaximize = document.getElementById('btn-toggle-layout-maximize');
    if (btnMaximize) {
        btnMaximize.classList.toggle('hidden', activeTab === 'sync');
    }

    const isYearScope = (activeTab === 'dashboard' && state.viewMode === 'list' && state.listScope === 'year') ||
                        (activeTab === 'creditcards' && state.ccViewMode === 'list' && state.ccListScope === 'year') ||
                        (activeTab === 'savings' && state.savingsViewMode === 'list' && state.savingsListScope === 'year');
    
    const headerPeriodNav = document.getElementById('header-period-nav');
    if (headerPeriodNav) {
        headerPeriodNav.classList.toggle('hidden', activeTab === 'sync');
    }
    
    const monthSelect = document.getElementById('month-select');
    if (monthSelect) {
        monthSelect.classList.toggle('hidden', isYearScope);
    }

    // Sync the cycle filter visibility and active button states
    const cycleFilterContainer = document.getElementById('cycle-filter-container');
    if (cycleFilterContainer) {
        const showCycleFilter = activeTab === 'dashboard' && state.viewMode === 'list' && state.listScope === 'month';
        cycleFilterContainer.classList.toggle('hidden', !showCycleFilter);
        
        if (showCycleFilter) {
            document.querySelectorAll('#cycle-filter-container .segment-btn').forEach(btn => {
                btn.classList.toggle('active', btn.dataset.cycle === (state.listCycleFilter || 'all'));
            });
        }
    }

    if (activeTab === 'dashboard') {
        renderDashboardTab();
    } else if (activeTab === 'bills') {
        renderBillsTab();
    } else if (activeTab === 'delivery') {
        renderDeliveryTab();
    } else if (activeTab === 'savings') {
        renderSavingsTab();
    } else if (activeTab === 'loans') {
        renderLoansTab();
    } else if (activeTab === 'creditcards') {
        renderCreditCardsTab();
    } else if (activeTab === 'billtracker') {
        renderBillTrackerTab();
    }
}

function getSavingsToday() {
    return formatLocalDate(new Date());
}

function getSavingsPeriodBounds(year, month, scope = 'month') {
    if (scope === 'year') return { start: `${year}-01-01`, end: `${year}-12-31` };
    const monthIndex = MONTH_ORDER.indexOf(month);
    const mm = String(monthIndex + 1).padStart(2, '0');
    const lastDay = String(new Date(year, monthIndex + 1, 0).getDate()).padStart(2, '0');
    return { start: `${year}-${mm}-01`, end: `${year}-${mm}-${lastDay}` };
}

function getSavingsTransactionsForPeriod(year, month, scope = 'month') {
    const { start, end } = getSavingsPeriodBounds(year, month, scope);
    return (state.savingsTransactions || [])
        .filter(tx => tx.date >= start && tx.date <= end)
        .sort((a, b) => a.date.localeCompare(b.date) || String(a.id).localeCompare(String(b.id)));
}

function getSavingsStartingBalance() {
    return Number(state.savingsStartingBalance ?? state.savingsCurrentAmount) || 0;
}

function getSavingsProjectedBalanceAtDate(date, inclusive = true) {
    return (state.savingsTransactions || [])
        .filter(tx => inclusive ? tx.date <= date : tx.date < date)
        .reduce((balance, tx) => balance + Number(tx.amount || 0), getSavingsStartingBalance());
}

function findPersonalSavingsMirror(transferId) {
    let match = null;
    Object.entries(state.personalCalendar || {}).some(([key, list]) => {
        const tx = list.find(item => item.transferId === transferId && item.savingsTransfer);
        if (!tx) return false;
        match = { key, list, tx };
        return true;
    });
    return match;
}

function syncSavingsPersonalMirror(tx, createIfMissing = false) {
    if (!tx?.transferId) return;
    const existing = findPersonalSavingsMirror(tx.transferId);
    if ((tx.kind || 'transfer') === 'interest') {
        if (existing) existing.list.splice(existing.list.indexOf(existing.tx), 1);
        return;
    }
    if (!existing && (tx.personalMirrorDetached || !createIfMissing)) return;
    const dateObj = new Date(tx.date + 'T00:00:00');
    const month = MONTH_ORDER[dateObj.getMonth()];
    const targetKey = `${dateObj.getFullYear()}-${month}`;
    ensureYearMonthInitialized(dateObj.getFullYear(), month);
    const mirror = existing?.tx || {
        id: 'p-' + Math.random().toString(36).substr(2, 9),
        transferId: tx.transferId,
        savingsTransfer: true
    };
    mirror.date = tx.date;
    mirror.description = tx.description;
    mirror.amount = -Number(tx.amount || 0);
    mirror.savingsTransfer = true;
    if (existing && existing.key !== targetKey) existing.list.splice(existing.list.indexOf(existing.tx), 1);
    if (!existing || existing.key !== targetKey) state.personalCalendar[targetKey].push(mirror);
}

function addLinkedSavingsTransfer(date, description, savingsAmount) {
    const amount = Number(savingsAmount);
    if (!date || !description || !Number.isFinite(amount) || amount === 0) return false;
    state.savingsTransactions = state.savingsTransactions || [];
    const tx = {
        id: 's-' + Math.random().toString(36).substr(2, 9),
        date,
        description,
        amount,
        kind: 'transfer',
        transferId: 'savings-xfer-' + Math.random().toString(36).substr(2, 9),
        savingsTransfer: true,
        personalMirrorDetached: false
    };
    state.savingsTransactions.push(tx);
    syncSavingsPersonalMirror(tx, true);
    return true;
}

function addSavingsInterest(date, description, amount) {
    const interestAmount = Number(amount);
    if (!date || !description || !Number.isFinite(interestAmount) || interestAmount === 0) return false;
    state.savingsTransactions = state.savingsTransactions || [];
    state.savingsTransactions.push({
        id: 's-' + Math.random().toString(36).substr(2, 9),
        date,
        description,
        amount: interestAmount,
        kind: 'interest',
        savingsTransfer: false
    });
    return true;
}

function deleteSavingsTransaction(id) {
    const index = (state.savingsTransactions || []).findIndex(tx => tx.id === id);
    if (index < 0) return null;
    return state.savingsTransactions.splice(index, 1)[0];
}

function renderSavingsTab() {
    state.savingsTransactions = state.savingsTransactions || [];
    const isCalendar = state.savingsViewMode !== 'list';
    const scope = isCalendar ? 'month' : (state.savingsListScope || 'month');
    const today = getSavingsToday();
    const bounds = getSavingsPeriodBounds(state.currentYear, state.currentMonth, scope);
    const periodTransactions = getSavingsTransactionsForPeriod(state.currentYear, state.currentMonth, scope);
    const futureTransfers = periodTransactions.filter(tx => (tx.kind || 'transfer') === 'transfer' && tx.date > today);
    const projectedTransferNet = futureTransfers.reduce((sum, tx) => sum + Number(tx.amount || 0), 0);
    const projectedDeposits = futureTransfers.filter(tx => Number(tx.amount) > 0).reduce((sum, tx) => sum + Number(tx.amount), 0);
    const projectedWithdrawals = futureTransfers.filter(tx => Number(tx.amount) < 0).reduce((sum, tx) => sum + Math.abs(Number(tx.amount)), 0);
    const currentBalance = getSavingsProjectedBalanceAtDate(today);
    const endBalance = getSavingsProjectedBalanceAtDate(bounds.end);
    const completedCount = state.savingsTransactions.filter(tx => tx.date <= today).length;

    document.getElementById('savings-current-display').textContent = `${currentBalance < 0 ? '-' : ''}$${Math.abs(currentBalance).toFixed(2)}`;
    document.getElementById('savings-current-display').className = `card-value ${currentBalance >= 0 ? 'positive' : 'negative'}`;
    document.getElementById('savings-current-sub').textContent = `Starting balance plus ${completedCount} completed entr${completedCount === 1 ? 'y' : 'ies'} through ${today}`;
    document.getElementById('savings-current-amount').value = getSavingsStartingBalance().toFixed(2);
    document.getElementById('savings-period-total').textContent = futureTransfers.length ? `${projectedTransferNet < 0 ? '-' : '+'}$${Math.abs(projectedTransferNet).toFixed(2)}` : '$0.00';
    document.getElementById('savings-period-total').className = `card-value ${projectedTransferNet >= 0 ? 'positive' : 'negative'}`;
    document.getElementById('savings-period-total-sub').textContent = futureTransfers.length
        ? `${futureTransfers.length} future transfer${futureTransfers.length === 1 ? '' : 's'}: +$${projectedDeposits.toFixed(2)} in | -$${projectedWithdrawals.toFixed(2)} out`
        : 'No uncompleted transfers in the selected period';
    document.getElementById('savings-projected-display').textContent = `${endBalance < 0 ? '-' : ''}$${Math.abs(endBalance).toFixed(2)}`;
    document.getElementById('savings-projected-display').className = `card-value ${endBalance >= 0 ? 'positive' : 'negative'}`;
    document.getElementById('savings-projected-sub').textContent = bounds.end < today ? `Actual balance at ${bounds.end}` : `Projected balance at ${bounds.end}`;

    const yearEndBalance = getSavingsProjectedBalanceAtDate(`${state.currentYear}-12-31`);
    const yearEndCard = document.getElementById('savings-year-projection-display');
    if (yearEndCard) {
        yearEndCard.textContent = `${yearEndBalance < 0 ? '-' : ''}$${Math.abs(yearEndBalance).toFixed(2)}`;
        yearEndCard.className = `card-value ${yearEndBalance >= 0 ? 'positive' : 'negative'}`;
    }

    document.getElementById('savings-metrics-panel').classList.toggle('hidden', !!state.savingsMetricsCollapsed);
    document.getElementById('btn-toggle-savings-metrics').textContent = state.savingsMetricsCollapsed ? 'Show Metrics' : 'Hide Metrics';
    document.getElementById('savings-calendar-layout').classList.toggle('hidden', !isCalendar);
    document.getElementById('savings-calendar-view').classList.remove('hidden');
    document.getElementById('savings-list-view').classList.toggle('hidden', isCalendar);
    document.getElementById('savings-scope-toggle').classList.toggle('hidden', isCalendar);
    document.getElementById('savings-ledger-title').textContent = isCalendar ? 'Savings Calendar' : 'Savings Ledger';
    document.querySelectorAll('[data-savings-mode]').forEach(btn => btn.classList.toggle('active', btn.dataset.savingsMode === state.savingsViewMode));
    document.querySelectorAll('[data-savings-scope]').forEach(btn => btn.classList.toggle('active', btn.dataset.savingsScope === scope));

    const monthNumber = String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0');
    const defaultDate = `${state.currentYear}-${monthNumber}-01`;
    const dateInput = document.getElementById('savings-transfer-date');
    if (dateInput && !dateInput.value) dateInput.value = defaultDate;

    if (isCalendar) renderSavingsCalendar();
    else renderSavingsList(periodTransactions, bounds.start);
    renderSavingsYearSummary();
}

function renderSavingsCalendar() {
    const container = document.getElementById('savings-calendar-days');
    container.innerHTML = '';
    const monthIndex = MONTH_ORDER.indexOf(state.currentMonth);
    const firstDay = new Date(Date.UTC(state.currentYear, monthIndex, 1));
    const gridStart = new Date(firstDay);
    gridStart.setUTCDate(gridStart.getUTCDate() - firstDay.getUTCDay());
    const today = getSavingsToday();

    for (let i = 0; i < 42; i++) {
        const date = new Date(gridStart);
        date.setUTCDate(gridStart.getUTCDate() + i);
        const dateStr = date.toISOString().split('T')[0];
        const dayTransactions = (state.savingsTransactions || []).filter(tx => tx.date === dateStr).sort((a, b) => String(a.id).localeCompare(String(b.id)));
        const balance = getSavingsProjectedBalanceAtDate(dateStr);
        const cell = document.createElement('div');
        const isCurrentMonth = date.getUTCMonth() === monthIndex && date.getUTCFullYear() === state.currentYear;
        const todayStr = formatLocalDate(new Date());
        cell.className = `calendar-day ${isCurrentMonth ? '' : (date < firstDay ? 'prev-month' : 'next-month')}${dateStr === todayStr ? ' today-highlight' : ''}`;
        cell.dataset.date = dateStr;
        const items = dayTransactions.slice(0, 3).map(tx => {
            const kind = tx.kind || 'transfer';
            const futureClass = tx.date > today ? ' savings-projected-entry' : '';
            return `<div class="day-transaction-item ${kind === 'interest' ? 'income' : 'transfer'}${futureClass}" draggable="true" data-id="${tx.id}" data-date="${dateStr}" data-amount="${tx.amount}" title="${escapeHTML(tx.description)}"><span>${kind === 'interest' ? 'Interest: ' : ''}${escapeHTML(tx.description)}</span><span>${tx.amount >= 0 ? '+' : '-'}$${Math.abs(tx.amount).toFixed(0)}</span></div>`;
        }).join('');
        cell.innerHTML = `<div class="day-number-wrapper"><span class="day-number">${date.getUTCDate()}</span><span class="day-balance ${balance >= 0 ? 'positive' : 'negative'}">${balance < 0 ? '-' : ''}$${Math.abs(Math.round(balance))}</span></div><div class="day-transactions">${items}${dayTransactions.length > 3 ? `<div class="day-transaction-item muted-text">+${dayTransactions.length - 3} more</div>` : ''}</div>`;

        cell.querySelectorAll('.day-transaction-item[data-id]').forEach(item => {
            item.addEventListener('dragstart', event => {
                event.dataTransfer.setData('text/plain', JSON.stringify({ savingsId: item.dataset.id, date: item.dataset.date }));
                item.classList.add('dragging');
            });
            item.addEventListener('dragend', () => item.classList.remove('dragging'));
            item.addEventListener('dblclick', event => {
                event.stopPropagation();
                openSavingsEditDialog(item.dataset.id);
            });
        });
        cell.addEventListener('dragover', event => event.preventDefault());
        cell.addEventListener('dragenter', event => { event.preventDefault(); cell.classList.add('drag-hover'); });
        cell.addEventListener('dragleave', () => cell.classList.remove('drag-hover'));
        cell.addEventListener('drop', event => {
            event.preventDefault();
            cell.classList.remove('drag-hover');
            try {
                const data = JSON.parse(event.dataTransfer.getData('text/plain'));
                if (data.savingsId) moveSavingsTransaction(data.savingsId, dateStr);
            } catch (error) {
                console.error('Savings drop parsing error:', error);
            }
        });
        cell.querySelector('.day-number').addEventListener('click', event => {
            event.stopPropagation();
            showSavingsDayDetails(dateStr);
        });
        container.appendChild(cell);
    }
}

function moveSavingsTransaction(id, targetDate) {
    const tx = (state.savingsTransactions || []).find(item => item.id === id);
    if (!tx || tx.date === targetDate) return;
    tx.date = targetDate;
    syncSavingsPersonalMirror(tx, false);
    saveDatabase();
    renderApp();
    logSuccess(`Moved savings entry to ${targetDate}: ${tx.description}`);
}

function openSavingsEditDialog(id) {
    const tx = (state.savingsTransactions || []).find(item => item.id === id);
    if (!tx) return;
    document.getElementById('savings-edit-id').value = tx.id;
    document.getElementById('savings-edit-type').value = tx.kind || 'transfer';
    document.getElementById('savings-edit-date').value = tx.date;
    document.getElementById('savings-edit-description').value = tx.description;
    document.getElementById('savings-edit-amount').value = Number(tx.amount || 0);
    document.getElementById('savings-edit-dialog').showModal();
}

function showSavingsDayDetails(date) {
    const dialog = document.getElementById('savings-day-dialog');
    const content = document.getElementById('savings-day-dialog-content');
    const transactions = (state.savingsTransactions || []).filter(tx => tx.date === date).sort((a, b) => String(a.id).localeCompare(String(b.id)));
    const formatted = new Date(date + 'T00:00:00').toLocaleDateString('en-US', { weekday: 'long', year: 'numeric', month: 'long', day: 'numeric' });
    document.getElementById('savings-day-dialog-title').textContent = formatted;
    content.innerHTML = `<div class="savings-day-balance">End-of-day balance: <strong>${getSavingsProjectedBalanceAtDate(date) < 0 ? '-' : ''}$${Math.abs(getSavingsProjectedBalanceAtDate(date)).toFixed(2)}</strong></div>`;
    if (!transactions.length) content.insertAdjacentHTML('beforeend', '<p class="muted-text">No savings entries on this day.</p>');
    transactions.forEach(tx => {
        const row = document.createElement('div');
        row.className = 'highlight-item';
        row.innerHTML = `<div class="highlight-item-left"><span class="highlight-item-title">${escapeHTML(tx.description)}</span><span class="highlight-item-tag">${(tx.kind || 'transfer').toUpperCase()}</span></div><div class="savings-day-actions"><span class="highlight-item-amount ${tx.amount >= 0 ? 'income' : 'expense'}">${tx.amount >= 0 ? '+' : '-'}$${Math.abs(tx.amount).toFixed(2)}</span><button class="action-btn small-btn danger-btn">Delete</button></div>`;
        row.addEventListener('dblclick', () => { dialog.close(); openSavingsEditDialog(tx.id); });
        row.querySelector('button').addEventListener('click', event => {
            event.stopPropagation();
            if (!confirm(`Delete "${tx.description}" from the Savings ledger? The Personal ledger will not be changed.`)) return;
            deleteSavingsTransaction(tx.id);
            saveDatabase();
            renderApp();
            showSavingsDayDetails(date);
        });
        content.appendChild(row);
    });
    if (!dialog.open) dialog.showModal();
}

function renderSavingsList(transactions, periodStart) {
    const body = document.getElementById('savings-list-body');
    if (!transactions.length) {
        body.innerHTML = '<tr><td colspan="6" class="muted-text" style="text-align:center;">No savings entries in this period.</td></tr>';
        return;
    }
    let running = getSavingsProjectedBalanceAtDate(periodStart, false);
    const today = getSavingsToday();
    body.innerHTML = transactions.map(tx => {
        running += Number(tx.amount || 0);
        const kind = tx.kind || 'transfer';
        const status = tx.date > today ? ' (PROJECTED)' : '';
        return `<tr class="savings-editable-row" data-id="${tx.id}" style="cursor:pointer;"><td>${tx.date}</td><td>${escapeHTML(tx.description)}</td><td><span class="day-transaction-item ${kind === 'interest' ? 'income' : 'transfer'}" style="display:inline-block;">${kind.toUpperCase()}${status}</span></td><td class="${tx.amount >= 0 ? 'positive' : 'negative'}">${tx.amount >= 0 ? '+' : '-'}$${Math.abs(tx.amount).toFixed(2)}</td><td class="${running >= 0 ? 'positive' : 'negative'}">${running < 0 ? '-' : ''}$${Math.abs(running).toFixed(2)}</td><td><button class="action-btn small-btn danger-btn delete-savings-entry" data-id="${tx.id}">Delete</button></td></tr>`;
    }).join('');
    body.querySelectorAll('.savings-editable-row').forEach(row => row.addEventListener('dblclick', () => openSavingsEditDialog(row.dataset.id)));
    body.querySelectorAll('.delete-savings-entry').forEach(button => button.addEventListener('click', event => {
        event.stopPropagation();
        if (!confirm('Delete this entry from Savings? The Personal ledger will not be changed.')) return;
        deleteSavingsTransaction(button.dataset.id);
        saveDatabase();
        renderApp();
    }));
}

function renderSavingsYearSummary() {
    const year = state.currentYear;
    const body = document.getElementById('savings-year-summary-body');
    const foot = document.getElementById('savings-year-summary-foot');
    document.getElementById('savings-year-summary-title').textContent = `Yearly Savings Summary - ${year}`;
    let totalIn = 0;
    let totalOut = 0;
    let totalInterest = 0;
    let totalNet = 0;
    const rows = MONTH_ORDER.map((month, index) => {
        const txs = getSavingsTransactionsForPeriod(year, month, 'month');
        const transfersIn = txs.filter(tx => (tx.kind || 'transfer') === 'transfer' && Number(tx.amount) > 0).reduce((sum, tx) => sum + Number(tx.amount), 0);
        const withdrawals = txs.filter(tx => (tx.kind || 'transfer') === 'transfer' && Number(tx.amount) < 0).reduce((sum, tx) => sum + Math.abs(Number(tx.amount)), 0);
        const interest = txs.filter(tx => tx.kind === 'interest').reduce((sum, tx) => sum + Number(tx.amount || 0), 0);
        const net = txs.reduce((sum, tx) => sum + Number(tx.amount || 0), 0);
        const endDate = `${year}-${String(index + 1).padStart(2, '0')}-${String(new Date(year, index + 1, 0).getDate()).padStart(2, '0')}`;
        const endBalance = getSavingsProjectedBalanceAtDate(endDate);
        totalIn += transfersIn;
        totalOut += withdrawals;
        totalInterest += interest;
        totalNet += net;
        return `<tr><td><strong>${MONTH_NAMES[month]}</strong></td><td class="positive">+$${transfersIn.toFixed(2)}</td><td class="negative">-$${withdrawals.toFixed(2)}</td><td class="${interest >= 0 ? 'positive' : 'negative'}">${interest >= 0 ? '+' : '-'}$${Math.abs(interest).toFixed(2)}</td><td class="${net >= 0 ? 'positive' : 'negative'}">${net >= 0 ? '+' : '-'}$${Math.abs(net).toFixed(2)}</td><td class="${endBalance >= 0 ? 'positive' : 'negative'}">${endBalance < 0 ? '-' : ''}$${Math.abs(endBalance).toFixed(2)}</td></tr>`;
    });
    const yearEnd = getSavingsProjectedBalanceAtDate(`${year}-12-31`);
    body.innerHTML = rows.join('');
    foot.innerHTML = `<tr><th>Total / Projection</th><th class="positive">+$${totalIn.toFixed(2)}</th><th class="negative">-$${totalOut.toFixed(2)}</th><th class="${totalInterest >= 0 ? 'positive' : 'negative'}">${totalInterest >= 0 ? '+' : '-'}$${Math.abs(totalInterest).toFixed(2)}</th><th class="${totalNet >= 0 ? 'positive' : 'negative'}">${totalNet >= 0 ? '+' : '-'}$${Math.abs(totalNet).toFixed(2)}</th><th class="${yearEnd >= 0 ? 'positive' : 'negative'}">${yearEnd < 0 ? '-' : ''}$${Math.abs(yearEnd).toFixed(2)}</th></tr>`;
    document.getElementById('savings-year-projection').textContent = `${yearEnd < 0 ? '-' : ''}$${Math.abs(yearEnd).toFixed(2)}`;
    document.getElementById('savings-year-projection').className = yearEnd >= 0 ? 'positive' : 'negative';
    document.getElementById('savings-year-summary-content').classList.toggle('hidden', !!state.savingsYearSummaryCollapsed);
    document.getElementById('savings-year-summary-caption').classList.toggle('hidden', !!state.savingsYearSummaryCollapsed);
    document.getElementById('btn-toggle-savings-year').textContent = state.savingsYearSummaryCollapsed ? 'Show Details' : 'Hide Details';
}
function getWeeksForYear(year) {
    const weeks = [];
    const start = new Date(year, 0, 1);
    const day = start.getDay();
    const diffToMonday = day === 0 ? -6 : 1 - day;
    const currentMonday = new Date(start);
    currentMonday.setDate(start.getDate() + diffToMonday);
    
    // Safety break counter (max 60 weeks in a year)
    let safetyCounter = 0;
    while (safetyCounter < 60) {
        safetyCounter++;
        const week = [];
        for (let i = 0; i < 7; i++) {
            const date = new Date(currentMonday);
            date.setDate(currentMonday.getDate() + i);
            week.push(ensureDeliveryEarningForDate(date));
        }
        
        const sunday = week[6];
        const sunDateObj = new Date(sunday.date + 'T00:00:00');
        if (sunDateObj.getFullYear() === year) {
            weeks.push(week);
        } else if (sunDateObj.getFullYear() > year) {
            break;
        }
        
        currentMonday.setDate(currentMonday.getDate() + 7);
    }
    return weeks;
}

function renderDeliveryYearSummary() {
    const year = state.currentYear;
    const container = document.getElementById('delivery-year-summary-content');
    if (!container) return;
    
    const formatVal = (val) => {
        const isNeg = val < 0;
        const formatted = Math.abs(val).toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 });
        return `${isNeg ? '-' : ''}$${formatted}`;
    };
    
    document.getElementById('delivery-year-summary-title').textContent = `Yearly Weekly Delivery Summary - ${year}`;
    
    // Calculate yearly totals
    const monthlyWeeks = getWeeksGroupedByMonth(year);
    let yearlyCash = 0;
    let yearlySideGigs = 0;
    let yearlyGrubHub = 0;
    let yearlyUberEats = 0;
    let yearlyBudget = 0;
    let yearlyActual = 0;
    
    MONTH_ORDER.forEach((month) => {
        const mWeeks = monthlyWeeks[month];
        mWeeks.forEach(week => {
            week.forEach(g => {
                yearlyCash += g.cash || 0;
                yearlySideGigs += g.sideGigs || 0;
                yearlyGrubHub += g.grubHub || 0;
                yearlyUberEats += g.uberEats || 0;
                yearlyActual += g.total || 0;
                yearlyBudget += Number(state.deliveryBudgets?.[g.date]) || 0;
            });
        });
    });
    
    const yearlyDiff = yearlyActual - yearlyBudget;
    const yearlyDiffClass = yearlyDiff > 0 ? 'positive' : (yearlyDiff < 0 ? 'negative' : '');
    const yearlyDiffSign = yearlyDiff > 0 ? '+' : '';
    
    const totalsHeader = document.getElementById('delivery-year-summary-totals-header');
    if (totalsHeader) {
        totalsHeader.innerHTML = `
            <div class="yearly-totals-summary-container">
                <div class="platform-totals">
                    <span>Cash: <strong>${formatVal(yearlyCash)}</strong></span>
                    <span>DoorDash: <strong>${formatVal(yearlySideGigs)}</strong></span>
                    <span>Grubhub: <strong>${formatVal(yearlyGrubHub)}</strong></span>
                    <span>UberEats: <strong>${formatVal(yearlyUberEats)}</strong></span>
                </div>
                <div class="overall-totals">
                    <span>Budget: <strong>${formatVal(yearlyBudget)}</strong></span>
                    <span>Actual: <strong>${formatVal(yearlyActual)}</strong></span>
                    <span class="${yearlyDiffClass}">Diff: <strong>${yearlyDiffSign}${formatVal(yearlyDiff)}</strong></span>
                </div>
            </div>
        `;
    }
    
    container.classList.toggle('hidden', !!state.deliveryYearSummaryCollapsed);
    document.getElementById('btn-toggle-delivery-year').textContent = state.deliveryYearSummaryCollapsed ? 'Show Details' : 'Hide Details';
    
    if (state.deliveryYearSummaryCollapsed) {
        container.innerHTML = '';
        return;
    }
    
    let html = '';
    
    MONTH_ORDER.forEach((month) => {
        const mWeeks = monthlyWeeks[month];
        if (mWeeks.length === 0) return;
        
        let monthBudget = 0;
        let monthActual = 0;
        
        const weekRowsHtml = mWeeks.map((week, wIdx) => {
            const pureWeekBudget = week.reduce((sum, g) => sum + (Number(state.deliveryBudgets?.[g.date]) || 0), 0);
            const pureWeekActual = week.reduce((sum, g) => sum + g.total, 0);
            
            monthBudget += pureWeekBudget;
            monthActual += pureWeekActual;
            
            const monStr = new Date(week[0].date + 'T00:00:00').toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
            const sunStr = new Date(week[6].date + 'T00:00:00').toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
            
            const diff = pureWeekActual - pureWeekBudget;
            const diffClass = diff > 0 ? 'positive' : diff < 0 ? 'negative' : '';
            const diffSign = diff > 0 ? '+' : '';
            
            return `
                <tr>
                    <td><strong>Week ${wIdx + 1}</strong></td>
                    <td class="muted-text">${monStr} - ${sunStr}</td>
                    <td style="text-align: right;">${formatVal(pureWeekBudget)}</td>
                    <td style="text-align: right; font-weight: 600;">${formatVal(pureWeekActual)}</td>
                    <td class="${diffClass}" style="text-align: right; font-weight: 500;">
                        ${diffSign}${formatVal(diff)}
                    </td>
                </tr>
            `;
        }).join('');
        
        const mDiff = monthActual - monthBudget;
        const mDiffClass = mDiff > 0 ? 'positive' : mDiff < 0 ? 'negative' : '';
        const mDiffSign = mDiff > 0 ? '+' : '';
        
        html += `
            <details class="month-summary-details" open>
                <summary class="month-summary-header">
                    <span>📁 ${MONTH_NAMES[month]}</span>
                    <div class="month-totals">
                        <span>Budget: <strong>${formatVal(monthBudget)}</strong></span>
                        <span>Actual: <strong>${formatVal(monthActual)}</strong></span>
                        <span class="${mDiffClass}">Diff: <strong>${mDiffSign}${formatVal(mDiff)}</strong></span>
                    </div>
                </summary>
                <div class="month-summary-table-wrapper">
                    <table class="data-table">
                        <thead>
                            <tr>
                                <th>Week</th>
                                <th>Date Range</th>
                                <th style="text-align: right;">Budgeted Goal</th>
                                <th style="text-align: right;">Actual Earnings</th>
                                <th style="text-align: right;">Variance</th>
                            </tr>
                        </thead>
                        <tbody>
                            ${weekRowsHtml}
                        </tbody>
                    </table>
                </div>
            </details>
        `;
    });
    
    container.innerHTML = html;
}

function getCalculatedTransferForJason(year, monthShort, cycle) {
    const cacheKey = `${year}-${monthShort}-${cycle}`;
    if (Object.prototype.hasOwnProperty.call(_transferForJasonCache, cacheKey)) return _transferForJasonCache[cacheKey];

    const key = `${year}-${monthShort}`;
    const mIdx = MONTH_ORDER.indexOf(monthShort);
    const mm = String(mIdx + 1).padStart(2, '0');
    const dd = cycle === '1st' ? '01' : '15';
    const cycleDate = `${year}-${mm}-${dd}`;
    const skippedTransfers = state.skippedTransfers || [];
    if (skippedTransfers.includes(cycleDate)) { _transferForJasonCache[cacheKey] = 0; return 0; }

    ensureYearMonthInitialized(year, monthShort);
    const mBills = state.monthlyBills[key];
    if (!mBills) { _transferForJasonCache[cacheKey] = 0; return 0; }

    autopopulateBillsForMonth(year, monthShort);
    applyAllocationTemplatesForMonth(year, monthShort);
    applySeasonalExpensesForMonth(year, monthShort);
    applySeasonalChargeForMonth(year, monthShort);

    const allBills = ['cycle1st', 'cycle15th'].flatMap(cycleKey => (mBills[cycleKey].bills || []).map(bill => normalizeBillSplitterItem(bill, cycleKey)));
    const cycleKey = cycle === '1st' ? 'cycle1st' : 'cycle15th';
    const cycleData = mBills[cycleKey];

    let jointBudget = 0;
    allBills.forEach(bill => {
        const assignedCycle = bill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st';
        const allocatedAmount = bill.cycleAllocation === 'both' ? bill.budgetAmount / 2 : (assignedCycle === cycleKey ? bill.budgetAmount : 0);
        if (bill.ownership !== 'personal') jointBudget += allocatedAmount;
    });

    // Preserve sign: negative "offset" allocations are meant to net against other allocations, not
    // add to them. 'both'-cycle allocations are stored once (in cycle1st) with cycle:'both' and
    // split half/half across both cycles, mirroring how 'both'-cycle bills are already split.
    const jasonAllocations = getAllocationCycleTotal(mBills, cycleKey, 'jason');
    const jointShare = Math.round(jointBudget * 50 + 1e-8) / 100;
    const jasonResult = Math.round((jasonAllocations + jointShare) * 100 + 1e-8) / 100;
    _transferForJasonCache[cacheKey] = jasonResult;
    return jasonResult;
}

function getCalculatedTransferForAsia(year, monthShort, cycle) {
    const cacheKey = `${year}-${monthShort}-${cycle}`;
    if (Object.prototype.hasOwnProperty.call(_transferForAsiaCache, cacheKey)) return _transferForAsiaCache[cacheKey];

    const key = `${year}-${monthShort}`;
    const mIdx = MONTH_ORDER.indexOf(monthShort);
    const mm = String(mIdx + 1).padStart(2, '0');
    const dd = cycle === '1st' ? '01' : '15';
    const cycleDate = `${year}-${mm}-${dd}`;
    const skippedTransfers = state.skippedTransfers || [];
    if (skippedTransfers.includes(cycleDate)) { _transferForAsiaCache[cacheKey] = 0; return 0; }

    ensureYearMonthInitialized(year, monthShort);
    const mBills = state.monthlyBills[key];
    if (!mBills) { _transferForAsiaCache[cacheKey] = 0; return 0; }

    autopopulateBillsForMonth(year, monthShort);
    applyAllocationTemplatesForMonth(year, monthShort);
    applySeasonalExpensesForMonth(year, monthShort);
    applySeasonalChargeForMonth(year, monthShort);

    const allBills = ['cycle1st', 'cycle15th'].flatMap(cycleKey => (mBills[cycleKey].bills || []).map(bill => normalizeBillSplitterItem(bill, cycleKey)));
    const cycleKey = cycle === '1st' ? 'cycle1st' : 'cycle15th';
    const cycleData = mBills[cycleKey];

    let jointBudget = 0;
    allBills.forEach(bill => {
        const assignedCycle = bill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st';
        const allocatedAmount = bill.cycleAllocation === 'both' ? bill.budgetAmount / 2 : (assignedCycle === cycleKey ? bill.budgetAmount : 0);
        if (bill.ownership !== 'personal') jointBudget += allocatedAmount;
    });

    // Preserve sign: negative "offset" allocations are meant to net against other allocations, not add to them.
    const asiaAllocations = getAllocationCycleTotal(mBills, cycleKey, 'asia');
    const jointShare = Math.round(jointBudget * 50 + 1e-8) / 100;
    const asiaResult = Math.round((asiaAllocations + jointShare) * 100 + 1e-8) / 100;
    _transferForAsiaCache[cacheKey] = asiaResult;
    return asiaResult;
}

// Caches for getPersonalRunningBalanceAtDate/getJointRunningBalanceAtDate, keyed by the target date
// (plus the includeDeliveryEarnings flag for the personal one). Cleared in saveDatabase().
let _personalRunningBalanceCache = {};
let _jointRunningBalanceCache = {};

// Both balance functions used to rescan every month of history from the beginning on every call, so
// a never-before-requested date paid the full O(history) cost even after the per-month building
// blocks were cached. These now build on month-boundary "checkpoints": the balance as of the start of
// month X is the checkpoint for the month before X plus that month's full (unconditional) contribution
// — computed once per month and reused via recursion, so a new date only pays for months that have
// never been checkpointed before instead of the whole history every time. Cleared in saveDatabase().
let _sortedPersonalCalendarKeysCache = null;
let _personalMonthFullContributionCache = { true: {}, false: {} };
let _personalMonthStartCheckpointCache = { true: {}, false: {} };
let _jointRegisterSortedCache = null;
let _jointMonthFullContributionCache = {};
let _jointDynamicCheckpointCache = {};

function getSortedPersonalCalendarKeys() {
    if (_sortedPersonalCalendarKeysCache) return _sortedPersonalCalendarKeysCache;
    _sortedPersonalCalendarKeysCache = Object.keys(state.personalCalendar).sort((a, b) => {
        const [yA, mA] = a.split('-');
        const [yB, mB] = b.split('-');
        if (parseInt(yA) !== parseInt(yB)) return parseInt(yA) - parseInt(yB);
        return MONTH_ORDER.indexOf(mA) - MONTH_ORDER.indexOf(mB);
    });
    return _sortedPersonalCalendarKeysCache;
}

// Unconditional (full-month) contribution to the personal balance from a single "year-month" key:
// both cycle transfers plus every transaction in the month, with no date cutoff. Valid to sum for any
// month that lies entirely before the target date.
function getPersonalMonthFullContribution(key, includeDeliveryEarnings) {
    const cache = _personalMonthFullContributionCache[includeDeliveryEarnings];
    if (Object.prototype.hasOwnProperty.call(cache, key)) return cache[key];

    const [yStr, mStr] = key.split('-');
    const y = parseInt(yStr);
    let contribution = -getCalculatedTransferForJason(y, mStr, '1st') - getCalculatedTransferForJason(y, mStr, '15th');

    getPersonalTransactionsForPeriod(y, mStr).forEach(tx => {
        if (tx.description === 'Xfer to Joint' && !tx.transferId) return;
        if (!includeDeliveryEarnings && tx.id.startsWith('dynamic-delivery-')) return;
        contribution += tx.amount;
    });

    cache[key] = contribution;
    return contribution;
}

// Balance as of the very start of the given month (i.e. before any of that month's own transactions),
// equal to the opening balance plus every full month-contribution strictly before it.
function getPersonalBalanceCheckpointBeforeMonth(year, monthShort, includeDeliveryEarnings) {
    const key = `${year}-${monthShort}`;
    const cache = _personalMonthStartCheckpointCache[includeDeliveryEarnings];
    if (Object.prototype.hasOwnProperty.call(cache, key)) return cache[key];

    // Flat forward walk, not recursion, and the running total lives in a local variable rather than
    // being re-derived through the cache at each step. Jumping straight to a month years in the future
    // materializes every never-before-seen month along the way, and each one can trigger a real
    // saveDatabase() (e.g. an installment loan's first automatic payment) — which clears this cache.
    // A recursive version paid for that by re-deriving every earlier month's checkpoint from scratch on
    // every single wipe (O(months²) work, synchronously — the actual cause of the freeze). Accumulating
    // locally means a wipe only costs a cheap re-lookup of that one month's own contribution, not a
    // redo of everything before it.
    const targetOrder = year * 12 + MONTH_ORDER.indexOf(monthShort);
    const priorKeys = getSortedPersonalCalendarKeys().filter(k => {
        const [yS, mS] = k.split('-');
        return parseInt(yS) * 12 + MONTH_ORDER.indexOf(mS) < targetOrder;
    });

    let balance = 2500;
    priorKeys.forEach(k => {
        balance += getPersonalMonthFullContribution(k, includeDeliveryEarnings);
    });

    _personalMonthStartCheckpointCache[includeDeliveryEarnings][key] = balance;
    return balance;
}

function getPersonalRunningBalanceAtDate(targetDateStr, includeDeliveryEarnings = true) {
    const cacheKey = `${targetDateStr}-${includeDeliveryEarnings}`;
    if (Object.prototype.hasOwnProperty.call(_personalRunningBalanceCache, cacheKey)) return _personalRunningBalanceCache[cacheKey];

    const targetTime = new Date(targetDateStr + 'T00:00:00').getTime();
    const targetDateObj = new Date(targetDateStr + 'T00:00:00');
    const y = targetDateObj.getFullYear();
    const mStr = MONTH_ORDER[targetDateObj.getMonth()];
    const mIdx = targetDateObj.getMonth();

    let balance = getPersonalBalanceCheckpointBeforeMonth(y, mStr, includeDeliveryEarnings);

    // Partial contribution from the target month itself — only the transfers/transactions that fall
    // strictly before targetDateStr, mirroring the original day-level cutoff behavior.
    const key = `${y}-${mStr}`;
    if (state.personalCalendar[key]) {
        const date1stStr = `${y}-${String(mIdx + 1).padStart(2, '0')}-01`;
        if (new Date(date1stStr + 'T00:00:00').getTime() < targetTime) {
            balance -= getCalculatedTransferForJason(y, mStr, '1st');
        }
        const date15thStr = `${y}-${String(mIdx + 1).padStart(2, '0')}-15`;
        if (new Date(date15thStr + 'T00:00:00').getTime() < targetTime) {
            balance -= getCalculatedTransferForJason(y, mStr, '15th');
        }
        getPersonalTransactionsForPeriod(y, mStr).forEach(tx => {
            if (tx.description === 'Xfer to Joint' && !tx.transferId) return;
            if (!includeDeliveryEarnings && tx.id.startsWith('dynamic-delivery-')) return;
            if (new Date(tx.date + 'T00:00:00').getTime() < targetTime) {
                balance += tx.amount;
            }
        });
    }

    _personalRunningBalanceCache[cacheKey] = balance;
    return balance;
}

// Sorted joint register with a running prefix sum, so "sum of all entries before date X" is a binary
// search + array lookup instead of a full re-filter/re-sort/re-scan of the register on every call.
function getSortedJointRegisterWithPrefix() {
    if (_jointRegisterSortedCache) return _jointRegisterSortedCache;
    const register = [...state.jointRegister]
        .filter(tx => !tx.billOccurrenceDeleted && !(tx.type === 'contribution' && !tx.transferId))
        .sort((a, b) => new Date(a.date).getTime() - new Date(b.date).getTime());

    const times = new Array(register.length);
    const prefix = new Array(register.length + 1);
    prefix[0] = 0;
    register.forEach((tx, i) => {
        times[i] = new Date(tx.date + 'T00:00:00').getTime();
        prefix[i + 1] = prefix[i] + (tx.type !== 'balance' ? tx.amount : 0);
    });

    _jointRegisterSortedCache = { times, prefix };
    return _jointRegisterSortedCache;
}

// Full (unconditional) 1st+15th Jason+Asia transfer contribution for a single joint month.
function getJointMonthFullContribution(year, monthShort) {
    const key = `${year}-${monthShort}`;
    if (Object.prototype.hasOwnProperty.call(_jointMonthFullContributionCache, key)) return _jointMonthFullContributionCache[key];
    const contribution = getCalculatedTransferForJason(year, monthShort, '1st') + getCalculatedTransferForAsia(year, monthShort, '1st')
        + getCalculatedTransferForJason(year, monthShort, '15th') + getCalculatedTransferForAsia(year, monthShort, '15th');
    _jointMonthFullContributionCache[key] = contribution;
    return contribution;
}

// Sum of every joint month's full dynamic-transfer contribution strictly before the given month,
// starting from the 2027 split-tracking start year. Flat forward walk with a local accumulator (see
// getPersonalBalanceCheckpointBeforeMonth above for why: a recursive version re-derives every earlier
// month from scratch each time a materialized-month side effect wipes this cache mid-walk).
function getJointDynamicCheckpointBeforeMonth(year, monthShort) {
    const key = `${year}-${monthShort}`;
    if (Object.prototype.hasOwnProperty.call(_jointDynamicCheckpointCache, key)) return _jointDynamicCheckpointCache[key];

    const startYear = 2027;
    const targetOrder = year * 12 + MONTH_ORDER.indexOf(monthShort);
    const startOrder = startYear * 12;

    let balance = 0;
    for (let order = startOrder; order < targetOrder; order++) {
        const y = Math.floor(order / 12);
        const mStr = MONTH_ORDER[((order % 12) + 12) % 12];
        balance += getJointMonthFullContribution(y, mStr);
    }

    _jointDynamicCheckpointCache[key] = balance;
    return balance;
}

function getJointRunningBalanceAtDate(targetDateStr) {
    if (Object.prototype.hasOwnProperty.call(_jointRunningBalanceCache, targetDateStr)) return _jointRunningBalanceCache[targetDateStr];

    const targetTime = new Date(targetDateStr + 'T00:00:00').getTime();
    const jan1_2027 = new Date('2027-01-01T00:00:00').getTime();
    let balance = targetTime >= jan1_2027 ? 1939.42 : 0;

    // Binary search for how many sorted register entries fall strictly before targetTime, then look up
    // their precomputed prefix sum instead of re-scanning the whole register.
    const { times, prefix } = getSortedJointRegisterWithPrefix();
    let lo = 0, hi = times.length;
    while (lo < hi) {
        const mid = (lo + hi) >> 1;
        if (times[mid] < targetTime) lo = mid + 1; else hi = mid;
    }
    balance += prefix[lo];

    // Add dynamic contributions up to targetTime (2027+ only)
    const startYear = 2027;
    const targetDateObj = new Date(targetDateStr + 'T00:00:00');
    const ty = targetDateObj.getFullYear();
    const tmStr = MONTH_ORDER[targetDateObj.getMonth()];
    const tmIdx = targetDateObj.getMonth();

    if (ty >= startYear) {
        balance += getJointDynamicCheckpointBeforeMonth(ty, tmStr);

        const date1stStr = `${ty}-${String(tmIdx + 1).padStart(2, '0')}-01`;
        if (new Date(date1stStr + 'T00:00:00').getTime() < targetTime) {
            balance += getCalculatedTransferForJason(ty, tmStr, '1st');
            balance += getCalculatedTransferForAsia(ty, tmStr, '1st');
        }
        const date15thStr = `${ty}-${String(tmIdx + 1).padStart(2, '0')}-15`;
        if (new Date(date15thStr + 'T00:00:00').getTime() < targetTime) {
            balance += getCalculatedTransferForJason(ty, tmStr, '15th');
            balance += getCalculatedTransferForAsia(ty, tmStr, '15th');
        }
    }

    _jointRunningBalanceCache[targetDateStr] = balance;
    return balance;
}

// 1. RENDER SUMMARY CARDS (Top dashboard indicators)
function renderSummaryCards() {
    const year = state.currentYear;
    const month = state.currentMonth;
    const key = `${year}-${month}`;
    
    ensureYearMonthInitialized(year, month);
    
    // Get card elements
    const cardNet = document.getElementById('net-cash-flow').closest('.summary-card');
    const cardBills = document.getElementById('joint-bills-total').closest('.summary-card');
    const cardGigs = document.getElementById('gig-earnings-total').closest('.summary-card');
    const cardBal = document.getElementById('card-remaining-balance');

    const isPersonal = state.dashboardType === 'personal';
    
    // Toggle overall visibility of joint bills and side gig cards
    if (cardBills) cardBills.classList.toggle('hidden', isPersonal);
    if (cardGigs) cardGigs.classList.toggle('hidden', !isPersonal);

    // Compute side gig earnings dynamically using the assigned weeks grouping
    const monthlyWeeks = getWeeksGroupedByMonth(year);
    const mWeeks = monthlyWeeks[month] || [];
    
    let monthProjectedGross = 0;
    let monthActualGross = 0;
    let allDaysActualized = true;

    mWeeks.forEach(week => {
        week.forEach(gRecord => {
            const isActualized = !!(gRecord.offDayReason || gRecord.total > 0 || gRecord.noEarnCash || gRecord.noEarnSideGigs || gRecord.noEarnGrubHub || gRecord.noEarnUberEats);
            if (!isActualized) {
                allDaysActualized = false;
            }
            
            monthActualGross += gRecord.total || 0;
            
            if (gRecord.offDayReason) {
                // Off day: contribution is 0
            } else if (isActualized) {
                monthProjectedGross += gRecord.total;
            } else {
                monthProjectedGross += Number(state.deliveryBudgets?.[gRecord.date]) || 0;
            }
        });
    });
    
    const taxProjected = monthProjectedGross * CONFIG.taxRate;
    const taxActual = monthActualGross * CONFIG.taxRate;

    if (isPersonal) {
        // --- PERSONAL DASHBOARD SUMMARY ---
        const personalTx = getPersonalTransactionsForPeriod(year, month).filter(tx => !(tx.description === 'Xfer to Joint' && !tx.transferId) && !tx.id.startsWith('dynamic-delivery-'));
        let personalInflow = 0;
        let personalOutflow = 0;

        personalTx.forEach(tx => {
            if (tx.amount > 0) personalInflow += tx.amount;
            else personalOutflow += tx.amount;
        });

        // Add dynamic transfers as outflows, using the same balance-adjusted amounts the
        // calendar/list views show (a transfer reduced for insufficient funds shouldn't be
        // counted here at its full, unreduced amount).
        const monthAdjustedTransfers = getAdjustedTransferAmountsForMonth(year, month);
        const amt1st = monthAdjustedTransfers[`xfer-1st-${year}-${month}`]?.amount || 0;
        const amt15th = monthAdjustedTransfers[`xfer-15th-${year}-${month}`]?.amount || 0;
        personalOutflow -= amt1st;
        personalOutflow -= amt15th;
        
        // Add gig earnings dynamically
        personalInflow += monthProjectedGross;
        personalOutflow -= taxProjected; // tax is outflow
        
        const netFlow = personalInflow + personalOutflow;

        // Card 1: Net Cash Flow
        if (cardNet) {
            cardNet.querySelector('.card-header span').textContent = 'Personal Net Cash Flow';
            cardNet.querySelector('.card-header .card-icon').textContent = '💵';
            const valEl = document.getElementById('net-cash-flow');
            valEl.textContent = `${netFlow >= 0 ? '' : '-'}$${Math.abs(netFlow).toFixed(2)}`;
            valEl.className = `card-value ${netFlow >= 0 ? 'positive' : 'negative'}`;
            document.getElementById('net-cash-flow-sub').textContent = `In: +$${personalInflow.toFixed(2)} | Out: -$${Math.abs(personalOutflow).toFixed(2)}`;
        }

        // Card 3: Side Gigs
        if (cardGigs) {
            document.getElementById('gig-earnings-total').textContent = `$${monthProjectedGross.toFixed(2)}`;
            document.getElementById('gig-earnings-sub').textContent = allDaysActualized
                ? `20% Tax Reserve: $${taxActual.toFixed(2)} (Actual)`
                : `20% Tax Reserve: $${taxProjected.toFixed(2)} (Proj)`;
        }

        // Card 4: Remaining Balance
        if (cardBal) {
            document.getElementById('remaining-balance-title').textContent = 'Personal Remaining Balance';
            
            const mIdx = MONTH_ORDER.indexOf(month);
            const nextMonth = mIdx === 11 ? 'Jan' : MONTH_ORDER[mIdx + 1];
            const nextYear = mIdx === 11 ? year + 1 : year;
            
            if (state.listScope === 'year' && state.viewMode === 'list') {
                const endYearDate = `${year + 1}-01-01`;
                const endBal = getPersonalRunningBalanceAtDate(endYearDate);
                const valBal = document.getElementById('remaining-balance-val');
                valBal.textContent = `$${endBal.toFixed(2)}`;
                valBal.className = `card-value ${endBal >= 0 ? 'positive' : 'negative'}`;
                document.getElementById('remaining-balance-sub').textContent = `End of Year ${year} projected balance`;
            } else {
                const date15th = `${year}-${String(mIdx + 1).padStart(2, '0')}-15`;
                const dateNextMonth1st = `${nextYear}-${String(MONTH_ORDER.indexOf(nextMonth) + 1).padStart(2, '0')}-01`;
                
                const bal1stCycle = getPersonalRunningBalanceAtDate(date15th);
                const bal2ndCycle = getPersonalRunningBalanceAtDate(dateNextMonth1st);
                
                const valBal = document.getElementById('remaining-balance-val');
                valBal.textContent = `$${bal2ndCycle.toFixed(2)}`;
                valBal.className = `card-value ${bal2ndCycle >= 0 ? 'positive' : 'negative'}`;
                document.getElementById('remaining-balance-sub').textContent = `End of 1st Cycle: $${bal1stCycle.toFixed(2)} | 2nd Cycle: $${bal2ndCycle.toFixed(2)}`;
            }
        }
    } else {
        // --- JOINT DASHBOARD SUMMARY ---
        const periodStart = state.listScope === 'month' ? `${state.currentYear}-${String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0')}-01` : `${state.currentYear}-01-01`;
        const periodEnd = state.listScope === 'month' ? `${state.currentYear}-${String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0')}-${String(new Date(state.currentYear, MONTH_ORDER.indexOf(state.currentMonth) + 1, 0).getDate()).padStart(2, '0')}` : `${state.currentYear}-12-31`;
        
        const monthsToSum = state.listScope === 'month' && state.viewMode === 'list' ? [month] : (state.listScope === 'year' && state.viewMode === 'list' ? MONTH_ORDER : [month]);
        let dynamicContributionsJason = 0;
        let dynamicContributionsAsia = 0;
        
        monthsToSum.forEach(m => {
            // Jason's side reflects the same balance-adjusted (possibly reduced) transfer amounts
            // shown on the calendar and list views; Asia's side has no such adjustment anywhere.
            const monthAdjustedTransfers = getAdjustedTransferAmountsForMonth(year, m);
            dynamicContributionsJason += (monthAdjustedTransfers[`xfer-1st-${year}-${m}`]?.amount || 0) + (monthAdjustedTransfers[`xfer-15th-${year}-${m}`]?.amount || 0);
            dynamicContributionsAsia += getCalculatedTransferForAsia(year, m, '1st') + getCalculatedTransferForAsia(year, m, '15th');
        });

        const manualContributions = state.jointRegister.filter(tx => tx.date >= periodStart && tx.date <= periodEnd && tx.type === 'contribution' && tx.transferId);
        const manualJason = manualContributions.reduce((sum, tx) => sum + (Number(tx.jason) || 0), 0);
        const manualAsia = manualContributions.reduce((sum, tx) => sum + (Number(tx.asia) || 0), 0);

        const jasonTotal = manualJason + dynamicContributionsJason;
        const asiaTotal = manualAsia + dynamicContributionsAsia;
        const totalContributions = jasonTotal + asiaTotal;

        // Card 1: Joint Contributions
        if (cardNet) {
            cardNet.querySelector('.card-header span').textContent = 'Joint Total Contributions';
            cardNet.querySelector('.card-header .card-icon').textContent = '👥';
            const valEl = document.getElementById('net-cash-flow');
            valEl.textContent = `$${totalContributions.toFixed(2)}`;
            valEl.className = `card-value ${totalContributions >= 0 ? 'positive' : 'negative'}`;
            document.getElementById('net-cash-flow-sub').textContent = `Jason: +$${jasonTotal.toFixed(2)} | Asia: +$${asiaTotal.toFixed(2)}`;
        }

        // Card 2: Joint Bills
        if (cardBills) {
            const mBills = state.monthlyBills[key];
            let jointTotal = 0;
            if (mBills) {
                jointTotal = (mBills.cycle1st?.totals?.billsTotal || 0) + (mBills.cycle15th?.totals?.billsTotal || 0);
            }
            document.getElementById('joint-bills-total').textContent = `$${jointTotal.toFixed(2)}`;
            document.getElementById('joint-bills-sub').textContent = `Cycle 1st: $${(mBills?.cycle1st?.totals?.billsTotal || 0).toFixed(2)} | Cycle 15th: $${(mBills?.cycle15th?.totals?.billsTotal || 0).toFixed(2)}`;
        }

        // Card 4: Remaining Balance
        if (cardBal) {
            document.getElementById('remaining-balance-title').textContent = 'Joint Remaining Balance';
            
            const mIdx = MONTH_ORDER.indexOf(month);
            const nextMonth = mIdx === 11 ? 'Jan' : MONTH_ORDER[mIdx + 1];
            const nextYear = mIdx === 11 ? year + 1 : year;

            if (state.listScope === 'year' && state.viewMode === 'list') {
                const endYearDate = `${year + 1}-01-01`;
                const endBal = getJointRunningBalanceAtDate(endYearDate);
                const valBal = document.getElementById('remaining-balance-val');
                valBal.textContent = `$${endBal.toFixed(2)}`;
                valBal.className = `card-value ${endBal >= 0 ? 'positive' : 'negative'}`;
                document.getElementById('remaining-balance-sub').textContent = `End of Year ${year} projected joint balance`;
            } else {
                const date15th = `${year}-${String(mIdx + 1).padStart(2, '0')}-15`;
                const dateNextMonth1st = `${nextYear}-${String(MONTH_ORDER.indexOf(nextMonth) + 1).padStart(2, '0')}-01`;
                
                const bal1stCycle = getJointRunningBalanceAtDate(date15th);
                const bal2ndCycle = getJointRunningBalanceAtDate(dateNextMonth1st);
                
                const valBal = document.getElementById('remaining-balance-val');
                valBal.textContent = `$${bal2ndCycle.toFixed(2)}`;
                valBal.className = `card-value ${bal2ndCycle >= 0 ? 'positive' : 'negative'}`;
                document.getElementById('remaining-balance-sub').textContent = `End of 1st Cycle: $${bal1stCycle.toFixed(2)} | 2nd Cycle: $${bal2ndCycle.toFixed(2)}`;
            }
        }
    }
}

// 2. RENDER DASHBOARD TAB (CALENDAR & LIST)
function renderDashboardTab() {
    const isCalendar = state.viewMode === 'calendar';
    document.getElementById('dashboard-calendar-view').classList.toggle('hidden', !isCalendar);
    document.getElementById('dashboard-list-view').classList.toggle('hidden', isCalendar);
    
    if (isCalendar) {
        renderCalendarDashboard();
    } else {
        renderListDashboard();
    }
}

function simulateJasonCheckingAndAdjustTransfers(daysData) {
    const adjustments = {
        transfers: {},
        deferred: []
    };
    
    let runningBalance = getPersonalRunningBalanceAtDate(daysData[0].date);
    let deferredBalance = 0;

    // The 42-day grid spans at most 3 distinct (year, month) pairs (the padding days before/after
    // the displayed month), so cache these two fairly expensive per-month lookups within this single
    // simulation pass instead of redoing them for every one of the ~30 days that share the same month.
    const txCache = {};
    const weeksCache = {};

    daysData.forEach(day => {
        const cellDateObj = new Date(day.date + 'T00:00:00');
        const cellYear = cellDateObj.getFullYear();
        const cellMonth = MONTH_ORDER[cellDateObj.getMonth()];
        const cellKey = `${cellYear}-${cellMonth}`;

        if (!txCache[cellKey]) txCache[cellKey] = getPersonalTransactionsForPeriod(cellYear, cellMonth);
        const cellTxList = txCache[cellKey];
        const matchedTx = cellTxList.filter(tx => tx.date === day.date && !(tx.description === 'Xfer to Joint' && !tx.transferId));

        let normalAmt = 0;
        matchedTx.forEach(tx => {
            normalAmt += tx.amount;
        });

        let deliveryAmt = 0;
        if (!weeksCache[cellMonth]) weeksCache[cellMonth] = getDeliveryWeeksForMonth(cellMonth);
        const weeks = weeksCache[cellMonth];
        const activeWeek = weeks.find(w => w.length && w[w.length - 1].date === day.date);
        if (activeWeek) {
            let weekGrossTotal = 0;
            let allActualized = true;
            activeWeek.forEach(gRecord => {
                const isActualized = !!(gRecord.offDayReason || gRecord.total > 0 || gRecord.noEarnCash || gRecord.noEarnSideGigs || gRecord.noEarnGrubHub || gRecord.noEarnUberEats);
                if (!isActualized) allActualized = false;
                if (!gRecord.offDayReason) {
                    if (isActualized) weekGrossTotal += gRecord.total;
                    else weekGrossTotal += Number(state.deliveryBudgets?.[gRecord.date]) || 0;
                }
            });
            if (weekGrossTotal > 0) {
                const depId = `dynamic-delivery-${day.date}`;
                const override = (state.dynamicOverrides || {})[depId];
                if (!override?.deleted) {
                    deliveryAmt = override?.amount !== undefined ? Math.abs(Number(override.amount) || 0) : weekGrossTotal;
                }
            }
        }
        
        runningBalance += normalAmt + deliveryAmt;
        
        const cellDayNum = cellDateObj.getDate();
        if (cellDayNum === 1 || cellDayNum === 15) {
            const cycleKey = cellDayNum === 1 ? '1st' : '15th';
            const dynId = `xfer-${cycleKey}-${cellYear}-${cellMonth}`;
            const ovr = (state.dynamicOverrides || {})[dynId];
            if (!ovr || !ovr.deleted) {
                const originalAmount = (ovr && ovr.amount !== undefined) ? Math.abs(ovr.amount) : getCalculatedTransferForJason(cellYear, cellMonth, cycleKey);
                if (originalAmount > 0) {
                    const available = Math.max(0, runningBalance);
                    if (available < originalAmount) {
                        const transferAmount = available;
                        const remainder = originalAmount - transferAmount;
                        
                        adjustments.transfers[dynId] = {
                            amount: transferAmount,
                            description: `${(ovr && ovr.description) || 'Xfer to Joint (Dynamic)'} (Reduced: covered $${transferAmount.toFixed(2)})`
                        };
                        deferredBalance += remainder;
                        runningBalance -= transferAmount;
                    } else {
                        adjustments.transfers[dynId] = {
                            amount: originalAmount,
                            description: (ovr && ovr.description) || 'Xfer to Joint (Dynamic)'
                        };
                        runningBalance -= originalAmount;
                    }
                }
            }
        }
        
        const isSunday = cellDateObj.getDay() === 0;
        if (deferredBalance > 0 && (isSunday || deliveryAmt > 0)) {
            const available = Math.max(0, runningBalance);
            if (available > 0) {
                const payAmount = Math.min(deferredBalance, available);
                deferredBalance -= payAmount;
                runningBalance -= payAmount;
                adjustments.deferred.push({
                    date: day.date,
                    amount: payAmount,
                    description: `Deferred Xfer to Joint (Dynamic)`
                });
            }
        }
    });
    
    return adjustments;
}

// Builds the 42-cell (6 week) calendar grid of day objects for a given month, used both to render
// the calendar view and to feed the balance-adjustment simulation so list views can be kept in sync.
function buildCalendarGridDates(year, monthShort) {
    const monthIndex = MONTH_ORDER.indexOf(monthShort);
    const firstDay = new Date(Date.UTC(year, monthIndex, 1));
    const startDayOfWeek = firstDay.getUTCDay();

    const gridStart = new Date(firstDay);
    gridStart.setUTCDate(gridStart.getUTCDate() - startDayOfWeek);

    const totalCells = 42; // 6 weeks
    const daysData = [];
    const tempDate = new Date(gridStart);

    for (let i = 0; i < totalCells; i++) {
        const dateStr = tempDate.toISOString().split('T')[0];
        const isCurrentMonth = tempDate.getUTCMonth() === monthIndex;
        daysData.push({
            date: dateStr,
            dayNum: tempDate.getUTCDate(),
            isCurrentMonth: isCurrentMonth,
            transactions: []
        });
        tempDate.setUTCDate(tempDate.getUTCDate() + 1);
    }
    return daysData;
}

// Cache for the Jason balance-adjustment simulation, keyed by "year-month". The simulation is
// expensive (walks a 42-day grid, re-deriving each day's transactions and delivery weeks), and the
// same month is requested repeatedly within a single renderApp() pass (summary cards, calendar,
// list views) and across renders where nothing changed (e.g. just switching tabs). Cleared in
// saveDatabase() so it never serves stale data after a real state change.
let _adjustedTransferCache = {};

// Returns the full {transfers, deferred} simulation result for a month, computing and caching it
// on first use. daysData is only needed on a cache miss.
function getSimulatedTransferAdjustmentsForMonth(year, monthShort, daysData) {
    const cacheKey = `${year}-${monthShort}`;
    if (_adjustedTransferCache[cacheKey]) return _adjustedTransferCache[cacheKey];
    const result = simulateJasonCheckingAndAdjustTransfers(daysData || buildCalendarGridDates(year, monthShort));
    _adjustedTransferCache[cacheKey] = result;
    return result;
}

// Returns the same balance-adjusted 1st/15th Jason transfer amounts (keyed by dynId) that the
// calendar view displays, so list views and editors can show the same reduced amount instead of
// independently recalculating the full, unreduced amount via getCalculatedTransferForJason.
function getAdjustedTransferAmountsForMonth(year, monthShort) {
    return getSimulatedTransferAdjustmentsForMonth(year, monthShort).transfers;
}

function renderCalendarDashboard() {
    const year = state.currentYear;
    const month = state.currentMonth;
    const monthIndex = MONTH_ORDER.indexOf(month);

    const calendarDaysContainer = document.getElementById('calendar-days');
    calendarDaysContainer.innerHTML = '';

    const daysData = buildCalendarGridDates(year, month);

    let dbModified = false;
    const adjustments = getSimulatedTransferAdjustmentsForMonth(year, month, daysData);
    
    // Populate transactions based on Personal vs Joint dashboard type
    if (state.dashboardType === 'personal') {
        // Personal Dashboard Calendar
        daysData.forEach(day => {
            const cellDateObj = new Date(day.date + 'T00:00:00');
            const cellYear = cellDateObj.getFullYear();
            const cellMonth = MONTH_ORDER[cellDateObj.getMonth()];
            const cellKey = `${cellYear}-${cellMonth}`;

            // Ensure month is initialized if templates exist
            ensureYearMonthInitialized(cellYear, cellMonth);

            const cellTxList = getPersonalTransactionsForPeriod(cellYear, cellMonth);
            // Filter out static Xfer to Joint without transferId
            const matchedTx = cellTxList.filter(tx => tx.date === day.date && !(tx.description === 'Xfer to Joint' && !tx.transferId));

            matchedTx.forEach(tx => {
                if (!tx.id) {
                    tx.id = 'p-' + Math.random().toString(36).substr(2, 9);
                    dbModified = true;
                }
                day.transactions.push({
                    id: tx.id,
                    description: tx.description,
                    amount: tx.amount,
                    type: tx.savingsTransfer || tx.description === 'Xfer to Joint' ? 'transfer' : (tx.amount > 0 ? 'income' : 'expense'),
                    isRecurring: !!tx.isRecurring, balanceTransferBy: tx.balanceTransferBy || '', transferId: tx.transferId || ''
                });
            });

            // Dynamic check for 1st or 15th
            const cellDayNum = cellDateObj.getDate();
            if (cellDayNum === 1 || cellDayNum === 15) {
                const cycleKey = cellDayNum === 1 ? '1st' : '15th';
                const dynId = `xfer-${cycleKey}-${cellYear}-${cellMonth}`;
                const adj = adjustments.transfers[dynId];
                if (adj && adj.amount > 0) {
                    day.transactions.push({
                        id: dynId,
                        description: adj.description,
                        amount: -adj.amount,
                        type: 'transfer',
                        isSplitterDynamic: true
                    });
                }
            }

            adjustments.deferred.forEach(def => {
                if (def.date === day.date) {
                    day.transactions.push({
                        id: `deferred-xfer-${day.date}`,
                        description: def.description,
                        amount: -def.amount,
                        type: 'transfer',
                        isSplitterDynamic: true,
                        isDeferredPayment: true
                    });
                }
            });
        });

        // Sort transactions and compute running balances
        let runningBalance = getPersonalRunningBalanceAtDate(daysData[0].date);
        daysData.forEach(day => {
            day.transactions.sort((a, b) => b.amount - a.amount);
            day.transactions.forEach(t => {
                runningBalance += t.amount;
            });
            day.balance = runningBalance;
        });
    } else if (state.dashboardType === 'joint') {
        // Joint Dashboard Calendar
        daysData.forEach(day => {
            const cellDateObj = new Date(day.date + 'T00:00:00');
            const cellYear = cellDateObj.getFullYear();
            const cellMonth = MONTH_ORDER[cellDateObj.getMonth()];

            // Filter out static contributions that don't have transferId
            const matchedTx = state.jointRegister.filter(tx => tx.date === day.date && !tx.billOccurrenceDeleted && !(tx.type === 'contribution' && !tx.transferId));

            matchedTx.forEach(tx => {
                if (tx.type !== 'balance') {
                    if (!tx.id) {
                        tx.id = 'j-' + Math.random().toString(36).substr(2, 9);
                        dbModified = true;
                    }
                    day.transactions.push({
                        id: tx.id,
                        description: tx.name,
                        amount: tx.amount,
                        type: tx.type === 'contribution' ? 'income' : 'expense',
                        isRecurring: !!tx.isRecurring, balanceTransferBy: tx.balanceTransferBy || '', transferId: tx.transferId || '', jason: tx.jason, asia: tx.asia, contributionRecipient: tx.contributionRecipient
                    });
                }
            });

            // Dynamic check for 1st or 15th (joint calendar)
            const cellDayNum = cellDateObj.getDate();
            if (cellDayNum === 1 || cellDayNum === 15) {
                const cycleKey = cellDayNum === 1 ? '1st' : '15th';
                
                const dynId = `xfer-${cycleKey}-${cellYear}-${cellMonth}`;
                const adj = adjustments.transfers[dynId];
                if (adj && adj.amount > 0) {
                    const jDynId = `joint-xfer-jason-${cycleKey}-${cellYear}-${cellMonth}`;
                    day.transactions.push({
                        id: jDynId,
                        description: adj.description.replace('Xfer to Joint', 'Jason Joint Contribution'),
                        amount: adj.amount,
                        type: 'income',
                        isSplitterDynamic: true
                    });
                }

                const aDynId = `joint-xfer-asia-${cycleKey}-${cellYear}-${cellMonth}`;
                const aOvr = (state.dynamicOverrides || {})[aDynId];
                if (!aOvr || !aOvr.deleted) {
                    const asiaAmt = (aOvr && aOvr.amount !== undefined) ? Math.abs(aOvr.amount) : getCalculatedTransferForAsia(cellYear, cellMonth, cycleKey);
                    if (asiaAmt !== 0) {
                        day.transactions.push({
                            id: aDynId,
                            description: (aOvr && aOvr.description) || 'Asia Joint Contribution (Dynamic)',
                            amount: asiaAmt,
                            type: 'income',
                            isSplitterDynamic: true
                        });
                    }
                }
            }

            adjustments.deferred.forEach(def => {
                if (def.date === day.date) {
                    day.transactions.push({
                        id: `deferred-joint-contrib-${day.date}`,
                        description: `Deferred Jason Joint Contribution (Dynamic)`,
                        amount: def.amount,
                        type: 'income',
                        isSplitterDynamic: true,
                        isDeferredPayment: true
                    });
                }
            });
        });

        // Sort transactions and compute running balances
        let runningBalance = getJointRunningBalanceAtDate(daysData[0].date);
        daysData.forEach(day => {
            day.transactions.sort((a, b) => b.amount - a.amount);
            day.transactions.forEach(t => {
                runningBalance += t.amount;
            });
            day.balance = runningBalance;
        });
    } else {
        // Credit Card Dashboard Calendar
        const cardId = state.dashboardType;
        daysData.forEach(day => {
            const cellDateObj = new Date(day.date + 'T00:00:00');
            const cellYear = cellDateObj.getFullYear();
            const cellMonth = MONTH_ORDER[cellDateObj.getMonth()];
            const cellKey = `${cellYear}-${cellMonth}`;
            
            // Ensure card calendar is initialized
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
            if (!state.cardCalendars[cardId][cellKey]) state.cardCalendars[cardId][cellKey] = [];
            
            const cellTxList = state.cardCalendars[cardId][cellKey];
            const matchedTx = cellTxList.filter(tx => tx.date === day.date && !tx.billOccurrenceDeleted);
            
            matchedTx.forEach(tx => {
                if (!tx.id) {
                    tx.id = 'c-' + Math.random().toString(36).substr(2, 9);
                    dbModified = true;
                }
                day.transactions.push({
                    id: tx.id,
                    description: tx.description,
                    amount: tx.amount,
                    type: tx.amount >= 0 ? 'income' : 'expense',
                    isRecurring: !!tx.isRecurring, balanceTransferBy: tx.balanceTransferBy || ''
                });
            });
        });
        
        // Sort transactions and compute running balances owed (debt owed is positive)
        let runningBalance = getCardRunningBalanceAtDate(cardId, daysData[0].date);
        daysData.forEach(day => {
            day.transactions.sort((a, b) => b.amount - a.amount);
            day.transactions.forEach(t => {
                if (t.amount < 0) {
                    runningBalance += Math.abs(t.amount);
                } else {
                    runningBalance -= t.amount;
                }
            });
            day.balance = runningBalance;
        });
    }
    
    if (dbModified) {
        saveDatabase();
    }
    window.activeCalendarDays = daysData;
    
    // Draw cells in the DOM
    daysData.forEach(day => {
        const dayCell = document.createElement('div');
        const todayStr = formatLocalDate(new Date());
        dayCell.className = `calendar-day ${day.isCurrentMonth ? '' : 'next-month'} ${day.date === state.selectedDate ? 'selected-day' : ''}${day.date === todayStr ? ' today-highlight' : ''}`;
        dayCell.dataset.date = day.date;
        
        const balanceColorClass = (state.dashboardType !== 'personal' && state.dashboardType !== 'joint')
            ? (day.balance > 0.01 ? 'negative' : 'positive')
            : (day.balance >= 0 ? 'positive' : 'negative');
        
        let txsHtml = '';
        day.transactions.slice(0, 3).forEach(t => {
            const typeClass = t.type;
            const isGig = t.isGig ? 'true' : 'false';
            
            txsHtml += `
                <div class="day-transaction-item ${typeClass}"
                     title="${escapeHTML(t.description)}: $${t.amount.toFixed(2)}${getClassificationTooltipSuffix(t)}"
                     draggable="true"
                     data-id="${t.id}"
                     data-date="${day.date}"
                     data-amount="${t.amount}"
                     data-isgig="${isGig}">
                    <span>${getTransactionIndicatorPrefix(t)}${escapeHTML(t.description)}</span>
                    <span>${t.amount >= 0 ? '+' : ''}${Math.round(t.amount)}</span>
                </div>
            `;
        });
        if (day.transactions.length > 3) {
            txsHtml += `<div class="day-transaction-item muted-text" style="background:none; text-align:center;">+${day.transactions.length - 3} more</div>`;
        }

        dayCell.innerHTML = `
            <div class="day-number-wrapper">
                <span class="day-number">${day.dayNum}</span>
                <span class="day-balance ${balanceColorClass}" title="Double-click to reconcile balance">$${Math.round(day.balance)}</span>
            </div>
            <div class="day-transactions">
                ${txsHtml}
            </div>
        `;
        
        // Bind transaction drag & drop and double click listeners
        dayCell.querySelectorAll('.day-transaction-item').forEach(txItem => {
            txItem.addEventListener('dragstart', (e) => {
                e.dataTransfer.setData('text/plain', JSON.stringify({
                    id: txItem.dataset.id,
                    date: txItem.dataset.date
                }));
                txItem.classList.add('dragging');
            });
            
            txItem.addEventListener('dragend', () => {
                txItem.classList.remove('dragging');
            });
            
            txItem.addEventListener('dblclick', (e) => {
                e.stopPropagation();
                const txId = txItem.dataset.id;
                const txDate = txItem.dataset.date;
                
                if (txItem.dataset.isgig === 'true') {
                    if (confirm(`Would you like to delete the side gig log for ${txDate}?`)) {
                        state.deliveryEarnings = state.deliveryEarnings.filter(g => g.date !== txDate);
                        saveDatabase();
                        renderApp();
                        logSystem(`Deleted side gig entry on ${txDate}`);
                    }
                    return;
                }
                
                if (isDynamicTxId(txId)) {
                    const currentDesc = txItem.querySelector('span') ? txItem.querySelector('span').textContent : '';
                    const currentAmt = parseFloat(txItem.dataset.amount || '0') || 0;
                    openDynamicTxEditor(txId, txDate, currentDesc, currentAmt);
                    return;
                }
                
                // Normal transaction edit
                openEditTransactionModal(txId, txDate);
            });
        });
        
        // Bind day cell as drag-over drop target
        dayCell.addEventListener('dragover', (e) => {
            e.preventDefault();
        });
        
        dayCell.addEventListener('dragenter', (e) => {
            e.preventDefault();
            dayCell.classList.add('drag-hover');
        });
        
        dayCell.addEventListener('dragleave', () => {
            dayCell.classList.remove('drag-hover');
        });
        
        dayCell.addEventListener('drop', (e) => {
            dayCell.classList.remove('drag-hover');
            const dataStr = e.dataTransfer.getData('text/plain');
            if (dataStr) {
                try {
                    const data = JSON.parse(dataStr);
                    moveTransaction(data.id, data.date, day.date);
                } catch (err) {
                    console.error("Drop parsing error:", err);
                }
            }
        });
        
        // Inline Balance Edit double-click listener
        const balanceSpan = dayCell.querySelector('.day-balance');
        balanceSpan.addEventListener('dblclick', (e) => {
            e.stopPropagation(); // Avoid triggering day select event
            
            const input = document.createElement('input');
            input.type = 'number';
            input.className = 'balance-edit-input';
            input.value = Math.round(day.balance);
            input.style.width = '65px';
            input.style.background = 'rgba(10, 15, 30, 0.9)';
            input.style.border = '1px solid var(--color-primary)';
            input.style.color = 'var(--text-primary)';
            input.style.borderRadius = '4px';
            input.style.padding = '1px 4px';
            input.style.textAlign = 'right';
            input.style.fontFamily = 'var(--font-heading)';
            input.style.fontSize = '0.8rem';
            input.style.fontWeight = '600';
            
            balanceSpan.replaceWith(input);
            input.focus();
            input.select();
            
            let finished = false;
            const saveEdit = () => {
                if (finished) return;
                finished = true;
                const newBalance = parseFloat(input.value);
                if (!isNaN(newBalance)) {
                    handleBalanceOverride(day.date, newBalance, day.balance);
                } else {
                    input.replaceWith(balanceSpan);
                }
            };
            
            input.addEventListener('blur', saveEdit);
            input.addEventListener('keydown', (evt) => {
                if (evt.key === 'Enter') {
                    saveEdit();
                } else if (evt.key === 'Escape') {
                    finished = true;
                    input.replaceWith(balanceSpan);
                }
            });
        });
        
        dayCell.addEventListener('click', () => {
            document.querySelectorAll('#calendar-days .calendar-day').forEach(c => c.classList.remove('selected-day'));
            dayCell.classList.add('selected-day');
            state.selectedDate = day.date;
            document.getElementById('trans-date').value = day.date;
        });
        dayCell.querySelector('.day-number').addEventListener('click', (e) => {
            e.stopPropagation();
            dayCell.click();
            renderDayHighlights(day);
            showDayHighlightsDialog('today-highlights-list');
        });
        
        calendarDaysContainer.appendChild(dayCell);
    });
}

function handleBalanceOverride(date, newBalance, oldBalance) {
    const diff = newBalance - oldBalance;
    if (Math.abs(diff) < 0.01) return; // Ignore if no change
    
    if (state.dashboardType === 'personal') {
        const dateObj = new Date(date + 'T00:00:00');
        const y = dateObj.getFullYear();
        const monthShort = MONTH_ORDER[dateObj.getMonth()];
        const key = `${y}-${monthShort}`;
        
        ensureYearMonthInitialized(y, monthShort);
        
        state.personalCalendar[key].push({
            id: 'p-' + Math.random().toString(36).substr(2, 9),
            date: date,
            description: "Balance Adjustment",
            amount: diff
        });
        
        logSystem(`Adjusted personal balance on ${date} from $${oldBalance.toFixed(2)} to $${newBalance.toFixed(2)} (Diff: ${diff >= 0 ? '+' : ''}$${diff.toFixed(2)})`);
    } else {
        // Joint Dashboard balance adjustment
        state.jointRegister.push({
            id: 'j-' + Math.random().toString(36).substr(2, 9),
            type: 'expense',
            name: "Balance Adjustment",
            amount: diff,
            date: date
        });
        
        logSystem(`Adjusted joint balance on ${date} from $${oldBalance.toFixed(2)} to $${newBalance.toFixed(2)} (Diff: ${diff >= 0 ? '+' : ''}$${diff.toFixed(2)})`);
    }
    
    saveDatabase();
    renderApp();
}

// Shows/hides the credit-card-payment notice in the edit-transaction dialog and applies the field
// restrictions for the checking-side legs of card payments: automatic payments allow only an amount
// override (date/description locked; the override touches neither the Bill Splitter budget nor the
// payment strategy), manual payments stay fully editable but get an informational notice, since
// changes propagate to the card ledger and the month's Bill Splitter row.
function applyEditTxCardPaymentNotice(tx) {
    const notice = document.getElementById('edit-tx-cc-payment-notice');
    const noticeText = document.getElementById('edit-tx-cc-payment-notice-text');
    const link = document.getElementById('edit-tx-cc-payment-link');
    const isAuto = !!(tx && tx.isAutomaticCardPayment);
    const isManualPmt = !isAuto && !!(tx && tx.payoffTargetId && tx.linkedPaymentId);
    if (!notice) return;
    if (!isAuto && !isManualPmt) { notice.classList.add('hidden'); return; }
    notice.classList.remove('hidden');
    const targetAccount = tx && tx.payoffTargetId ? state.loans.find(l => l.id === tx.payoffTargetId) : null;
    const accountLabel = targetAccount && targetAccount.type === 'loan' ? 'loan' : 'credit card';
    if (noticeText) {
        noticeText.textContent = isAuto
            ? `Automatic ${accountLabel} payment: only the amount can be changed here. The override will not affect the Bill Splitter budget or the ${accountLabel}’s automatic payment settings.`
            : `Scheduled ${accountLabel} payment: changes here also update the ${accountLabel}’s ledger and this month’s Bill Splitter entry.`;
    }
    if (isAuto) {
        document.getElementById('edit-tx-date').disabled = true;
        document.getElementById('edit-tx-desc').disabled = true;
    }
    if (link) {
        link.onclick = (e) => {
            e.preventDefault();
            goToCardPaymentInCreditCards(tx.payoffTargetId, tx.date);
        };
    }
}

function openEditTransactionModal(txId, date) {
    const dialog = document.getElementById('edit-tx-dialog');
    document.getElementById('edit-tx-id').value = txId;
    document.getElementById('edit-tx-date-orig').value = date;
    document.getElementById('edit-tx-date').value = date;
    document.getElementById('edit-tx-mode').value = 'edit';
    document.getElementById('edit-tx-modal-title').textContent = 'Edit Transaction';
    document.getElementById('btn-save-edit-tx').textContent = 'Save Changes';
    document.getElementById('btn-duplicate-edit-tx').classList.remove('hidden');
    // Reset card-payment notice state from any previous open
    const ccNotice = document.getElementById('edit-tx-cc-payment-notice');
    if (ccNotice) ccNotice.classList.add('hidden');
    document.getElementById('edit-tx-date').disabled = false;
    document.getElementById('edit-tx-desc').disabled = false;
    
    const contribGroup = document.getElementById('edit-joint-contrib-group');
    const amountGroup = document.getElementById('edit-amount-group');
    const merchantGroup = document.getElementById('edit-merchant-group');
    const merchantInput = document.getElementById('edit-tx-merchant');
    const cardMetaGroup = document.getElementById('edit-card-meta-group');
    const ownerInput = document.getElementById('edit-tx-owner');
    const tripInput = document.getElementById('edit-tx-trip');
    
    const recurringGroup = document.getElementById('edit-recurring-group');
    const recurringCheckbox = document.getElementById('edit-tx-recurring');
    const recurringDayGroup = document.getElementById('edit-recurring-day-group');
    const recurringDayInput = document.getElementById('edit-tx-recurring-day');
    
    // Determine if we are in a CC context (either sub-dashboard or main dashboard with CC selected)
    const isCCContext = !!state.ccSelectedCardId || (state.dashboardType !== 'personal' && state.dashboardType !== 'joint');
    
    // Show/hide merchant and recurring fields based on context
    merchantGroup.classList.toggle('hidden', !isCCContext);
    merchantInput.value = '';
    cardMetaGroup.classList.toggle('hidden', !isCCContext);
    ownerInput.value = 'personal';
    tripInput.value = '';
    
    recurringGroup.classList.toggle('hidden', !isCCContext);
    document.getElementById('edit-payment-plan-group').classList.toggle('hidden', !isCCContext);
    document.getElementById('edit-tx-payment-plan').checked = false;
    document.getElementById('edit-payment-plan-fields').classList.add('hidden');
    recurringCheckbox.checked = false;
    recurringDayGroup.classList.add('hidden');
    recurringDayInput.value = '';
    
    if (state.ccSelectedCardId) {
        // CC Sub-dashboard context
        const cardId = state.ccSelectedCardId;
        const dateObj = new Date(date + 'T00:00:00');
        const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
        const list = (state.cardCalendars && state.cardCalendars[cardId]) ? (state.cardCalendars[cardId][key] || []) : [];
        const tx = list.find(t => t.id === txId);
        if (tx) {
            if (tx.isAutomaticCardPayment) document.getElementById('edit-tx-modal-title').textContent = tx.automaticPaymentOverridden ? 'Edit Automatic Payment Override' : 'Override Automatic Payment';
            document.getElementById('edit-tx-desc').value = tx.description;
            document.getElementById('edit-tx-amount').value = Math.abs(tx.amount);
            merchantInput.value = tx.merchant || '';
            document.getElementById('edit-tx-kind').value = tx.transactionKind || (tx.amount < 0 ? 'charge' : 'payment');
            ownerInput.value = tx.owner || 'personal';
            tripInput.value = tx.trip || '';
            populateTransactionPaymentPlanFields(tx, cardId);
            document.getElementById('edit-payment-plan-group').classList.toggle('hidden', tx.amount >= 0);
            recurringGroup.classList.toggle('hidden', tx.amount >= 0);
            
            recurringCheckbox.checked = !!tx.isRecurring;
            if (tx.isRecurring) {
                recurringDayGroup.classList.remove('hidden');
                recurringDayInput.value = tx.recurringDay || '';
            }
            
            contribGroup.classList.add('hidden');
            amountGroup.classList.remove('hidden');
            dialog.showModal();
        }
    } else if (state.dashboardType === 'personal') {
        const dateObj = new Date(date + 'T00:00:00');
        const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
        const list = state.personalCalendar[key] || [];
        const tx = list.find(t => t.id === txId);
        if (tx) {
            if (tx.isAutomaticCardPayment) document.getElementById('edit-tx-modal-title').textContent = tx.automaticPaymentOverridden ? 'Edit Automatic Payment Override' : 'Override Automatic Payment';
            document.getElementById('edit-tx-desc').value = tx.description;
            document.getElementById('edit-tx-amount').value = tx.amount;
            contribGroup.classList.add('hidden');
            amountGroup.classList.remove('hidden');
            applyEditTxCardPaymentNotice(tx);
            dialog.showModal();
        }
    } else if (state.dashboardType === 'joint') {
        const tx = state.jointRegister.find(t => t.id === txId);
        if (tx) {
            if (tx.isAutomaticCardPayment) document.getElementById('edit-tx-modal-title').textContent = tx.automaticPaymentOverridden ? 'Edit Automatic Payment Override' : 'Override Automatic Payment';
            document.getElementById('edit-tx-desc').value = tx.name;
            if (tx.type === 'contribution') {
                document.getElementById('edit-tx-jason').value = tx.jason || 0;
                document.getElementById('edit-tx-asia').value = tx.asia || 0;
                contribGroup.classList.remove('hidden');
                amountGroup.classList.add('hidden');
            } else {
                document.getElementById('edit-tx-amount').value = Math.abs(tx.amount);
                contribGroup.classList.add('hidden');
                amountGroup.classList.remove('hidden');
            }
            applyEditTxCardPaymentNotice(tx);
            dialog.showModal();
        }
    } else {
        const cardId = state.dashboardType;
        const dateObj = new Date(date + 'T00:00:00');
        const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
        const list = (state.cardCalendars && state.cardCalendars[cardId]) ? (state.cardCalendars[cardId][key] || []) : [];
        const tx = list.find(t => t.id === txId);
        if (tx) {
            if (tx.isAutomaticCardPayment) document.getElementById('edit-tx-modal-title').textContent = tx.automaticPaymentOverridden ? 'Edit Automatic Payment Override' : 'Override Automatic Payment';
            document.getElementById('edit-tx-desc').value = tx.description;
            document.getElementById('edit-tx-amount').value = Math.abs(tx.amount);
            merchantInput.value = tx.merchant || '';
            document.getElementById('edit-tx-kind').value = tx.transactionKind || (tx.amount < 0 ? 'charge' : 'payment');
            ownerInput.value = tx.owner || 'personal';
            tripInput.value = tx.trip || '';
            populateTransactionPaymentPlanFields(tx, cardId);
            document.getElementById('edit-payment-plan-group').classList.toggle('hidden', tx.amount >= 0);
            recurringGroup.classList.toggle('hidden', tx.amount >= 0);
            
            recurringCheckbox.checked = !!tx.isRecurring;
            if (tx.isRecurring) {
                recurringDayGroup.classList.remove('hidden');
                recurringDayInput.value = tx.recurringDay || '';
            }
            
            contribGroup.classList.add('hidden');
            amountGroup.classList.remove('hidden');
            dialog.showModal();
        }
    }
}

function moveTransaction(txId, sourceDate, targetDate) {
    if (sourceDate === targetDate) return;

    const srcObj = new Date(sourceDate + 'T00:00:00');
    const srcYear = srcObj.getFullYear();
    const srcMonthShort = MONTH_ORDER[srcObj.getMonth()];
    
    const tgtObj = new Date(targetDate + 'T00:00:00');
    const tgtYear = tgtObj.getFullYear();
    const tgtMonthShort = MONTH_ORDER[tgtObj.getMonth()];
    const tgtKey = `${tgtYear}-${tgtMonthShort}`;

    // 1. Check if dragging a Side Gig
    if (txId && (txId.startsWith('gig-') || txId.startsWith('tax-'))) {
        const gig = state.deliveryEarnings.find(g => g.date === sourceDate);
        if (gig) {
            gig.date = targetDate;
            saveDatabase();
            renderApp();
            logSuccess(`Moved side gig earnings to ${targetDate}`);
            return;
        }
    }

    // 2. Check if dragging Jason's dynamic paycheck
    if (txId && txId.startsWith('dynamic-paycheck-')) {
        const paycheckAmount = getJasonPayrollAmount(srcYear, srcMonthShort, sourceDate);
        if (paycheckAmount > 0) {
            ensureYearMonthInitialized(tgtYear, tgtMonthShort);
            if (!state.personalCalendar[tgtKey]) state.personalCalendar[tgtKey] = [];
            state.personalCalendar[tgtKey].push({
                id: 'p-' + Math.random().toString(36).substr(2, 9),
                date: targetDate,
                description: 'Jason Pay (Manual Shift)',
                amount: paycheckAmount
            });
            // Mark the source date paycheck as skipped
            if (!state.payrollConfig.skippedPaychecks) state.payrollConfig.skippedPaychecks = [];
            state.payrollConfig.skippedPaychecks.push(sourceDate);
            saveDatabase();
            renderApp();
            logSuccess(`Shifted scheduled paycheck on ${sourceDate} to manual paycheck on ${targetDate}`);
            return;
        }
    }

    // 3. Check if dragging dynamic transfer to joint (e.g. xfer-1st-2026-Jul)
    if (txId && (txId.startsWith('xfer-1st-') || txId.startsWith('xfer-15th-'))) {
        const cycle = txId.includes('1st') ? '1st' : '15th';
        // Use the same balance-adjusted amount shown on the calendar, so materializing the
        // dragged transaction doesn't silently revert a reduced transfer back to its full amount.
        const srcAdjustedTransfers = getAdjustedTransferAmountsForMonth(srcYear, srcMonthShort);
        const transferAmount = srcAdjustedTransfers[`xfer-${cycle}-${srcYear}-${srcMonthShort}`]?.amount || 0;
        if (transferAmount > 0) {
            const transferId = 'checking-xfer-' + Math.random().toString(36).substr(2, 9);
            ensureYearMonthInitialized(tgtYear, tgtMonthShort);
            if (!state.personalCalendar[tgtKey]) state.personalCalendar[tgtKey] = [];
            state.personalCalendar[tgtKey].push({
                id: 'p-' + Math.random().toString(36).substr(2, 9),
                date: targetDate,
                description: 'Xfer to Joint',
                amount: -transferAmount,
                transferId: transferId
            });
            state.jointRegister.push({
                id: 'j-' + Math.random().toString(36).substr(2, 9),
                type: 'contribution',
                name: 'Xfer to Joint',
                jason: transferAmount,
                asia: 0,
                amount: transferAmount,
                date: targetDate,
                transferId: transferId
            });
            // Mark sourceDate as skipped transfer
            if (!state.skippedTransfers) state.skippedTransfers = [];
            const srcIdx = MONTH_ORDER.indexOf(srcMonthShort);
            const srcMM = String(srcIdx + 1).padStart(2, '0');
            const srcDD = cycle === '1st' ? '01' : '15';
            const cycleDateStr = `${srcYear}-${srcMM}-${srcDD}`;
            state.skippedTransfers.push(cycleDateStr);
            saveDatabase();
            renderApp();
            logSuccess(`Shifted scheduled joint transfer on ${cycleDateStr} to ${targetDate}`);
            return;
        }
    }

    // 4. Check if dragging dynamic joint contribution (from joint checking view)
    if (txId && (txId.startsWith('joint-xfer-jason-') || txId.startsWith('joint-xfer-asia-'))) {
        const cycle = txId.includes('1st') ? '1st' : '15th';
        // Jason's side uses the same balance-adjusted amount shown on the calendar; Asia's side
        // has no such adjustment anywhere in the app.
        const srcAdjustedTransfers = getAdjustedTransferAmountsForMonth(srcYear, srcMonthShort);
        const jasonAmt = srcAdjustedTransfers[`xfer-${cycle}-${srcYear}-${srcMonthShort}`]?.amount || 0;
        const asiaAmt = getCalculatedTransferForAsia(srcYear, srcMonthShort, cycle);
        const totalAmt = jasonAmt + asiaAmt;
        if (totalAmt > 0) {
            const transferId = 'checking-xfer-' + Math.random().toString(36).substr(2, 9);
            state.jointRegister.push({
                id: 'j-' + Math.random().toString(36).substr(2, 9),
                type: 'contribution',
                name: 'Joint Cycle Contribution',
                jason: jasonAmt,
                asia: asiaAmt,
                amount: totalAmt,
                date: targetDate,
                transferId: transferId
            });
            if (jasonAmt > 0) {
                ensureYearMonthInitialized(tgtYear, tgtMonthShort);
                if (!state.personalCalendar[tgtKey]) state.personalCalendar[tgtKey] = [];
                state.personalCalendar[tgtKey].push({
                    id: 'p-' + Math.random().toString(36).substr(2, 9),
                    date: targetDate,
                    description: 'Xfer to Joint',
                    amount: -jasonAmt,
                    transferId: transferId
                });
            }
            // Mark sourceDate as skipped transfer
            if (!state.skippedTransfers) state.skippedTransfers = [];
            const srcIdx = MONTH_ORDER.indexOf(srcMonthShort);
            const srcMM = String(srcIdx + 1).padStart(2, '0');
            const srcDD = cycle === '1st' ? '01' : '15';
            const cycleDateStr = `${srcYear}-${srcMM}-${srcDD}`;
            state.skippedTransfers.push(cycleDateStr);
            saveDatabase();
            renderApp();
            logSuccess(`Shifted scheduled joint contributions on ${cycleDateStr} to ${targetDate}`);
            return;
        }
    }

    // 5. Normal transaction dragging
    if (state.dashboardType === 'personal') {
        const srcKey = `${srcYear}-${srcMonthShort}`;
        const srcList = state.personalCalendar[srcKey] || [];
        const tx = srcList.find(t => t.id === txId);
        if (tx) {
            if (tx.linkedBillId) {
                tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date;
                tx.billOccurrenceOverridden = true;
                tx.billOccurrenceDeleted = false;
            }
            tx.date = targetDate;
            if (srcKey !== tgtKey) {
                const idx = srcList.indexOf(tx);
                srcList.splice(idx, 1);
                ensureYearMonthInitialized(tgtYear, tgtMonthShort);
                if (!state.personalCalendar[tgtKey]) state.personalCalendar[tgtKey] = [];
                state.personalCalendar[tgtKey].push(tx);
            }
            syncCheckingTransferMirror(tx, 'personal');
            logSuccess(`Moved personal transaction to ${targetDate}: ${tx.description}`);
        }
    } else if (state.dashboardType === 'joint') {
        const tx = state.jointRegister.find(t => t.id === txId);
        if (tx) {
            tx.date = targetDate;
            syncCheckingTransferMirror(tx, 'joint');
            logSuccess(`Moved joint transaction to ${targetDate}: ${tx.name}`);
        }
    } else {
        const cardId = state.dashboardType;
        const srcKey = `${srcYear}-${srcMonthShort}`;
        if (!state.cardCalendars) state.cardCalendars = {};
        if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
        const srcList = state.cardCalendars[cardId][srcKey] || [];
        const tx = srcList.find(t => t.id === txId);
        if (tx) {
            if (tx.linkedBillId) {
                tx.billOccurrenceDate = tx.billOccurrenceDate || tx.date;
                tx.billOccurrenceOverridden = true;
                tx.billOccurrenceDeleted = false;
            }
            tx.date = targetDate;
            if (srcKey !== tgtKey) {
                const idx = srcList.indexOf(tx);
                srcList.splice(idx, 1);
                if (!state.cardCalendars[cardId][tgtKey]) state.cardCalendars[cardId][tgtKey] = [];
                state.cardCalendars[cardId][tgtKey].push(tx);
            }
            logSuccess(`Moved credit card transaction to ${targetDate}: ${tx.description}`);
        }
    }
    
    saveDatabase();
    renderApp();
}

function getTransactionTransferPerson(tx) {
    if (tx.balanceTransferBy === 'jason') return 'Jason';
    if (tx.balanceTransferBy === 'asia') return 'Asia';
    const jason = Number(tx.jason) || 0;
    const asia = Number(tx.asia) || 0;
    if (jason !== 0 && asia !== 0) return 'Jason + Asia';
    if (jason !== 0 || tx.contributionRecipient === 'jason') return 'Jason';
    if (asia !== 0 || tx.contributionRecipient === 'asia') return 'Asia';
    if (tx.transferId) return 'Jason';
    return '';
}
function isBalanceTransferTransaction(tx) {
    const label = String(tx.description || tx.name || '');
    return !!(tx.balanceTransferBy || tx.transferId || /\b(?:bal(?:ance)?\s+transfer|xfer)\b/i.test(label));
}
// Classifies a ledger/calendar transaction as Manual or Dynamic (Credit Card / Loan payment leg),
// for the source-indicator badges shown across the ledger and Bill Splitter. Only transactions
// linked to a card/loan payoff target are ever "Dynamic" here — Bill Tracker bills never
// materialize into the personal/joint ledger, so "Bill" as a dynamic source only applies within
// the Bill Splitter's own row rendering (see getBillIndicatorBadge).
function getPaymentClassification(tx) {
    if (!tx || !tx.payoffTargetId) return null;
    const target = state.loans.find(l => l.id === tx.payoffTargetId);
    if (!target) return null;
    return {
        sourceType: target.type === 'loan' ? 'loan' : 'creditcard',
        sourceName: target.name,
        recurring: !!(tx.isAutomaticCardPayment || tx.automaticPaymentId),
        endDate: target.paymentEndDate || null
    };
}
// Short plain-text suffix (no HTML) describing Manual vs Dynamic classification, appended to
// calendar day-cell tooltips where there's no room for a visible badge.
function getClassificationTooltipSuffix(tx) {
    const classification = getPaymentClassification(tx);
    if (classification) {
        const typeLabel = classification.sourceType === 'loan' ? 'Loan' : 'Credit Card';
        const recurLabel = classification.recurring ? 'Recurring' : 'One-time';
        const endNote = classification.endDate ? `, ends ${classification.endDate}` : '';
        return ` — Dynamic: ${typeLabel} payment, ${recurLabel.toLowerCase()}${endNote}`;
    }
    if (!tx.linkedPaymentId && !tx.automaticPaymentId && !tx.isAutomaticCardPayment) {
        return ' — Manual entry';
    }
    return '';
}
// Bill Splitter equivalent of getTransactionIndicatorBadges — bill rows are a different shape
// (state.monthlyBills entries, not ledger transactions) and can additionally be Bill-Tracker-synced,
// which never happens in the ledger (Bill Tracker bills don't materialize into personalCalendar/
// jointRegister — they only ever live in state.monthlyBills).
function getBillIndicatorBadge(bill) {
    if (bill.billTrackerSettingId) {
        const categoryNote = bill.billTrackerCategory ? ` (${bill.billTrackerCategory})` : '';
        return `<span class="cc-source-badge manual" title="Dynamic entry — synced from Bill Tracker${categoryNote}">&#128203; Bill${categoryNote}</span>`;
    }
    if (bill.isMortgage) {
        const target = bill.mortgageLoanId ? state.loans.find(l => l.id === bill.mortgageLoanId) : null;
        const endNote = target && target.paymentEndDate ? `, ends ${target.paymentEndDate}` : '';
        return `<span class="cc-source-badge loan" title="Dynamic entry — Loan payment${target ? ` (${target.name})` : ''}, recurring${endNote}">&#127974; Loan &middot; Recurring</span>`;
    }
    if (bill.linkedCardPaymentId) {
        const target = bill.payoffTargetId ? state.loans.find(l => l.id === bill.payoffTargetId) : null;
        const isLoan = target && target.type === 'loan';
        const typeLabel = isLoan ? 'Loan' : 'Credit Card';
        const icon = isLoan ? '&#127974;' : '&#128179;';
        const recurLabel = bill.cardPaymentKind === 'auto' ? 'Recurring' : 'One-time';
        const endNote = target && target.paymentEndDate ? `, ends ${target.paymentEndDate}` : '';
        return `<span class="cc-source-badge ${isLoan ? 'loan' : 'creditcard'}" title="Dynamic entry — ${typeLabel} payment${target ? ` (${target.name})` : ''}, ${recurLabel.toLowerCase()}${endNote}">${icon} ${typeLabel} &middot; ${recurLabel}</span>`;
    }
    return '<span class="cc-source-badge manual" title="Manual entry">&#9998; Manual</span>';
}
function getTransactionIndicatorBadges(tx) {
    const recurring = tx.isRecurring ? '<span class="cc-recurring-badge" title="Recurring charge">&#8635; Recurring</span>' : '';
    const person = getTransactionTransferPerson(tx);
    const transfer = isBalanceTransferTransaction(tx) ? `<span class="cc-transfer-badge" title="Balance transfer">&#8644; Balance Transfer${person ? ` - ${person}` : ''}</span>` : '';
    const classification = getPaymentClassification(tx);
    let source = '';
    if (classification) {
        const typeLabel = classification.sourceType === 'loan' ? 'Loan' : 'Credit Card';
        const icon = classification.sourceType === 'loan' ? '&#127974;' : '&#128179;';
        const recurLabel = classification.recurring ? 'Recurring' : 'One-time';
        const endNote = classification.endDate ? `, ends ${classification.endDate}` : '';
        source = `<span class="cc-source-badge ${classification.sourceType}" title="Dynamic entry — ${typeLabel} payment (${classification.sourceName}), ${recurLabel.toLowerCase()}${endNote}">${icon} ${typeLabel} &middot; ${recurLabel}</span>`;
    } else if (!tx.linkedPaymentId && !tx.automaticPaymentId && !tx.isAutomaticCardPayment) {
        source = '<span class="cc-source-badge manual" title="Manual entry">&#9998; Manual</span>';
    }
    return `${recurring}${transfer}${source}`;
}
function getTransactionIndicatorPrefix(tx) {
    const recurring = tx.isRecurring ? '&#8635; ' : '';
    const person = getTransactionTransferPerson(tx);
    const classification = getPaymentClassification(tx);
    const sourceIcon = classification ? `${classification.sourceType === 'loan' ? '&#127974;' : '&#128179;'} ` : '';
    const transfer = isBalanceTransferTransaction(tx) ? `&#8644;${person === 'Jason' ? ' J' : person === 'Asia' ? ' A' : ''} ` : '';
    return sourceIcon + recurring + transfer;
}
function renderListDashboard() {
    if (state.dashboardType === 'personal') {
        renderPersonalList();
    } else if (state.dashboardType === 'joint') {
        renderJointList();
    } else {
        renderCardList();
    }
}

function renderCardList() {
    const cardId = state.dashboardType;
    const card = state.loans.find(c => c.id === cardId);
    if (!card) return;
    
    const container = document.getElementById('list-view-container');
    container.innerHTML = '';
    
    const year = state.currentYear;
    const cardCal = state.cardCalendars[cardId] || {};
    
    let txList = [];
    
    if (state.listScope === 'month') {
        const key = `${year}-${state.currentMonth}`;
        const txs = cardCal[key] || [];
        txs.forEach(t => {
            txList.push({ ...t, monthKey: key });
        });
    } else {
        // Full Year
        Object.keys(cardCal).forEach(key => {
            if (key.startsWith(`${year}-`)) {
                const txs = cardCal[key] || [];
                txs.forEach(t => {
                    txList.push({ ...t, monthKey: key });
                });
            }
        });
    }
    
    txList.sort((a, b) => new Date(a.date).getTime() - new Date(b.date).getTime());
    
    let balance = card.startBal || 0;
    if (txList.length > 0) {
        balance = getCardRunningBalanceAtDate(cardId, txList[0].date);
    }
    
    let rowsHtml = '';
    txList.forEach(t => {
        if (t.amount < 0) {
            balance += Math.abs(t.amount);
        } else {
            balance -= t.amount;
        }
        const dayName = new Date(t.date + 'T00:00:00').toLocaleDateString('en-US', { weekday: 'short' });
        
        rowsHtml += `
            <tr class="editable-row" data-id="${t.id}" data-date="${t.date}" style="cursor: pointer;">
                <td><strong>${t.date}</strong></td>
                <td><span class="card-icon info" style="font-size:0.75rem; padding: 2px 6px;">${dayName}</span></td>
                <td>${escapeHTML(t.description)} ${getTransactionIndicatorBadges(t)}</td>
                <td><span class="day-transaction-item ${t.amount < 0 ? 'expense' : 'income'}" style="display:inline-block; padding: 2px 6px; border-radius:4px; font-size:0.75rem;">${t.amount < 0 ? 'CHARGE' : 'PAYMENT'}</span></td>
                <td class="${t.amount < 0 ? 'negative' : 'positive'} font-heading" style="font-weight:600;">${t.amount >= 0 ? '+' : '-'}$${Math.abs(t.amount).toFixed(2)}</td>
                <td class="${balance > 0.01 ? 'negative' : 'positive'} font-heading" style="font-weight:600;">$${balance.toFixed(2)}</td>
                <td>
                    <button class="action-btn small-btn danger-btn delete-list-tx-btn" data-key="${t.monthKey}" data-id="${t.id}">Delete</button>
                </td>
            </tr>
        `;
    });
    
    if (txList.length === 0) {
        container.innerHTML = `<p class="muted-text" style="text-align:center; padding:2rem;">No card transactions logged for this period.</p>`;
        return;
    }
    
    container.innerHTML = `
        <table class="data-table">
            <thead>
                <tr>
                    <th>Date</th>
                    <th>Day</th>
                    <th>Description</th>
                    <th>Type</th>
                    <th>Amount</th>
                    <th>Running Balance Owed</th>
                    <th>Actions</th>
                </tr>
            </thead>
            <tbody>
                ${rowsHtml}
            </tbody>
        </table>
    `;
    
    container.querySelectorAll('.delete-list-tx-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            const key = e.target.dataset.key;
            const id = e.target.dataset.id;
            
            const list = state.cardCalendars[cardId][key] || [];
            const idx = list.findIndex(tx => tx.id === id);
            if (idx > -1) {
                const removed = list.splice(idx, 1)[0];
                saveDatabase();
                renderApp();
                logSystem(`Deleted card transaction: ${removed.description} ($${Math.abs(removed.amount).toFixed(2)})`);
            }
        });
    });

    container.querySelectorAll('.editable-row').forEach(row => {
        row.addEventListener('dblclick', () => {
            openEditTransactionModal(row.dataset.id, row.dataset.date);
        });
    });
}

// Global function to toggle list sorting
window.toggleListSort = function(key) {
    if (state.listSort.key === key) {
        state.listSort.direction = state.listSort.direction === 'asc' ? 'desc' : 'asc';
    } else {
        state.listSort.key = key;
        state.listSort.direction = 'asc';
    }
    renderApp();
};

function sortTransactions(list, sortConfig) {
    const key = sortConfig.key || 'date';
    const direction = sortConfig.direction || 'asc';
    
    return [...list].sort((a, b) => {
        const aIsDynamic = !!a.isSplitterDynamic;
        const bIsDynamic = !!b.isSplitterDynamic;
        
        if (key === 'date') {
            const cmp = a.date.localeCompare(b.date);
            if (cmp !== 0) {
                return direction === 'asc' ? cmp : -cmp;
            }
            if (aIsDynamic && !bIsDynamic) return -1;
            if (!aIsDynamic && bIsDynamic) return 1;
            return String(a.id).localeCompare(String(b.id));
        }
        
        let cmp = 0;
        if (key === 'description' || key === 'name') {
            const valA = (a.description || a.name || '').toLowerCase();
            const valB = (b.description || b.name || '').toLowerCase();
            cmp = valA.localeCompare(valB);
        } else if (key === 'amount') {
            cmp = (a.amount || 0) - (b.amount || 0);
        } else if (key === 'jason') {
            cmp = (Number(a.jason) || 0) - (Number(b.jason) || 0);
        } else if (key === 'asia') {
            cmp = (Number(a.asia) || 0) - (Number(b.asia) || 0);
        } else if (key === 'type') {
            cmp = (a.type || '').localeCompare(b.type || '');
        } else if (key === 'runningBalance') {
            cmp = (a.runningBalance || 0) - (b.runningBalance || 0);
        }
        
        if (direction === 'desc') {
            cmp = -cmp;
        }
        
        if (cmp === 0) {
            const dateCmp = a.date.localeCompare(b.date);
            if (dateCmp !== 0) return dateCmp;
            if (aIsDynamic && !bIsDynamic) return -1;
            if (!aIsDynamic && bIsDynamic) return 1;
            return String(a.id).localeCompare(String(b.id));
        }
        
        return cmp;
    });
}

function renderPersonalList() {
    const container = document.getElementById('list-view-table-container');
    document.getElementById('list-view-title').textContent = `Personal Checking Ledger (${state.listScope === 'month' ? MONTH_NAMES[state.currentMonth] + ' ' + state.currentYear : state.currentYear})`;
    
    let txList = [];
    const year = state.currentYear;
    const monthsToLoad = state.listScope === 'month' ? [state.currentMonth] : MONTH_ORDER;
    
    monthsToLoad.forEach(m => {
        const key = `${year}-${m}`;
        ensureYearMonthInitialized(year, m);
        
        const mTx = getPersonalTransactionsForPeriod(year, m).filter(tx => !(tx.description === 'Xfer to Joint' && !tx.transferId));
        mTx.forEach(tx => {
            txList.push({
                ...tx,
                type: tx.savingsTransfer || tx.description === 'Xfer to Joint' ? 'transfer' : (tx.amount > 0 ? 'income' : 'expense'),
                monthKey: key
            });
        });
        
        const mIdx = MONTH_ORDER.indexOf(m);
        const mPart = String(mIdx + 1).padStart(2, '0');
        const yStr = String(year);

        // Use the same balance-adjusted amounts the calendar view shows (including any
        // insufficient-funds reduction), instead of independently recalculating the full,
        // unreduced amount — otherwise this list can show a different dollar figure than the
        // calendar for the same real-world transfer.
        const monthAdjustedTransfers = getAdjustedTransferAmountsForMonth(year, m);

        const dynId1st = `xfer-1st-${year}-${m}`;
        const ovr1st = (state.dynamicOverrides || {})[dynId1st];
        if (!ovr1st || !ovr1st.deleted) {
            const adj1st = monthAdjustedTransfers[dynId1st];
            const amt1st = adj1st ? adj1st.amount : 0;
            if (amt1st !== 0) {
                txList.push({
                    id: dynId1st,
                    date: `${yStr}-${mPart}-01`,
                    description: (adj1st && adj1st.description) || 'Xfer to Joint (Dynamic)',
                    amount: -amt1st,
                    type: 'transfer',
                    isSplitterDynamic: true,
                    monthKey: key
                });
            }
        }

        const dynId15th = `xfer-15th-${year}-${m}`;
        const ovr15th = (state.dynamicOverrides || {})[dynId15th];
        if (!ovr15th || !ovr15th.deleted) {
            const adj15th = monthAdjustedTransfers[dynId15th];
            const amt15th = adj15th ? adj15th.amount : 0;
            if (amt15th !== 0) {
                txList.push({
                    id: dynId15th,
                    date: `${yStr}-${mPart}-15`,
                    description: (adj15th && adj15th.description) || 'Xfer to Joint (Dynamic)',
                    amount: -amt15th,
                    type: 'transfer',
                    isSplitterDynamic: true,
                    monthKey: key
                });
            }
        }
    });
    
    // Calculate running balance in chronological order first
    txList.sort((a, b) => {
        const dateCmp = a.date.localeCompare(b.date);
        if (dateCmp !== 0) return dateCmp;
        // Keep dynamic first
        if (a.isSplitterDynamic && !b.isSplitterDynamic) return -1;
        if (!a.isSplitterDynamic && b.isSplitterDynamic) return 1;
        return String(a.id).localeCompare(String(b.id));
    });
    
    let balance = 2500;
    if (txList.length > 0) {
        balance = getPersonalRunningBalanceAtDate(txList[0].date);
    }
    
    txList.forEach(t => {
        balance += t.amount;
        t.runningBalance = balance;
    });
    
    // Apply cycle filter (only in Month view)
    let filteredList = txList;
    if (state.listScope === 'month') {
        const cycleFilter = state.listCycleFilter || 'all';
        if (cycleFilter === '1st') {
            filteredList = txList.filter(t => parseInt(t.date.split('-')[2]) < 15);
        } else if (cycleFilter === '2nd') {
            filteredList = txList.filter(t => parseInt(t.date.split('-')[2]) >= 15);
        }
    }
    
    // Sort transactions based on user choice
    const sortedList = sortTransactions(filteredList, state.listSort);
    
    let rowsHtml = '';
    sortedList.forEach(t => {
        const typeClass = t.type;
        const dayName = new Date(t.date + 'T00:00:00').toLocaleDateString('en-US', { weekday: 'short' });
        const isEditableDynamic = isDynamicTxId(t.id);
        let actionHtml = '<span class="muted-text">—</span>';

        if (!t.isGig && isEditableDynamic) {
            actionHtml = `<button class="action-btn small-btn danger-btn hide-dynamic-list-tx-btn" data-id="${t.id}" data-date="${t.date}" data-desc="${escapeHTML(t.description)}">Delete</button>`;
        } else if (!t.isGig) {
            actionHtml = `<button class="action-btn small-btn danger-btn delete-list-tx-btn" data-id="${t.id}" data-key="${t.monthKey}" data-desc="${escapeHTML(t.description)}" data-date="${t.date}" data-amt="${t.amount}">Delete</button>`;
        }

        rowsHtml += `
            <tr class="editable-row" data-id="${t.id}" data-date="${t.date}" data-desc="${escapeHTML(t.description)}" data-amount="${t.amount}" data-isgig="${t.isGig ? 'true' : 'false'}" data-dynamic="${isEditableDynamic ? 'true' : 'false'}" style="cursor: pointer;">
                <td><strong>${t.date}</strong></td>
                <td><span class="card-icon info" style="font-size:0.75rem; padding: 2px 6px;">${dayName}</span></td>
                <td>${escapeHTML(t.description)} ${getTransactionIndicatorBadges(t)}</td>
                <td><span class="day-transaction-item ${typeClass}" style="display:inline-block; padding: 2px 6px; border-radius:4px; font-size:0.75rem;">${t.type.toUpperCase()}</span></td>
                <td class="${t.amount >= 0 ? 'positive' : 'negative'} font-heading" style="font-weight:600;">${t.amount >= 0 ? '+' : '-'}$${Math.abs(t.amount).toFixed(2)}</td>
                <td class="${t.runningBalance >= 0 ? 'positive' : 'negative'} font-heading" style="font-weight:600;">$${t.runningBalance.toFixed(2)}</td>
                <td>
                    ${actionHtml}
                </td>
            </tr>
        `;
    });
    
    if (sortedList.length === 0) {
        container.innerHTML = `<p class="muted-text" style="text-align:center; padding:2rem;">No personal transactions logged for this period.</p>`;
        return;
    }
    
    const getSortCaret = (colKey) => {
        if (state.listSort.key === colKey) {
            return state.listSort.direction === 'asc' ? ' ▲' : ' ▼';
        }
        return '';
    };

    container.innerHTML = `
        <table class="data-table">
            <thead>
                <tr>
                    <th style="cursor:pointer;" onclick="toggleListSort('date')">Date${getSortCaret('date')}</th>
                    <th>Day</th>
                    <th style="cursor:pointer;" onclick="toggleListSort('description')">Description${getSortCaret('description')}</th>
                    <th style="cursor:pointer;" onclick="toggleListSort('type')">Type${getSortCaret('type')}</th>
                    <th style="cursor:pointer;" onclick="toggleListSort('amount')">Amount${getSortCaret('amount')}</th>
                    <th style="cursor:pointer;" onclick="toggleListSort('runningBalance')">Running Balance${getSortCaret('runningBalance')}</th>
                    <th>Actions</th>
                </tr>
            </thead>
            <tbody>
                ${rowsHtml}
            </tbody>
        </table>
    `;
    
    container.querySelectorAll('.delete-list-tx-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            e.stopPropagation();
            const key = e.currentTarget.dataset.key;
            const id = e.currentTarget.dataset.id;
            const date = e.currentTarget.dataset.date;
            const desc = e.currentTarget.dataset.desc;
            const amt = parseFloat(e.currentTarget.dataset.amt);
            
            if (confirm(`Are you sure you want to delete "${desc}" on ${date}?`)) {
                const list = state.personalCalendar[key] || [];
                const idx = list.findIndex(tx => tx.id === id || (tx.date === date && tx.description === desc && Math.abs(tx.amount - amt) < 0.01));
                if (idx > -1) {
                    const transaction = list[idx];
                    if (transaction.isAutomaticCardPayment) {
                        alert('Automatic card payments cannot be deleted from the ledger. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
                        return;
                    }
                    if (transaction.linkedBillId) {
                        transaction.billOccurrenceDate = transaction.billOccurrenceDate || transaction.date;
                        transaction.billOccurrenceOverridden = true;
                        transaction.billOccurrenceDeleted = true;
                    } else {
                        const removed = list.splice(idx, 1)[0];
                        removeCheckingTransferMirror(removed, 'personal');
                        removeLinkedCardPaymentLeg(removed);
                    }
                    saveDatabase();
                    renderApp();
                    logSystem(`Deleted personal transaction on ${date}: ${desc} ($${amt.toFixed(2)})`);
                }
            }
        });
    });

    container.querySelectorAll('.hide-dynamic-list-tx-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            e.stopPropagation();
            const { id, date, desc } = e.currentTarget.dataset;
            const settingLabel = String(id).startsWith('dynamic-paycheck-') ? 'payroll schedule' : 'bill splitter settings';
            if (!confirm(`Are you sure you want to hide "${desc}" on ${date}? This does not change your ${settingLabel}.`)) return;

            saveDynamicTxOverride(id, { deleted: true });
            saveDatabase();
            renderApp();
            logSystem(`Hidden dynamic transaction ${id} on ${date}`);
        });
    });

    container.querySelectorAll('.editable-row').forEach(row => {
        row.addEventListener('dblclick', () => {
            if (row.dataset.isgig === 'true') return;
            if (row.dataset.id && row.dataset.id.startsWith('dynamic-delivery-')) {
                switchToTab('delivery');
                return;
            }
            if (row.dataset.dynamic === 'true') {
                openDynamicTxEditor(row.dataset.id, row.dataset.date, row.dataset.desc, parseFloat(row.dataset.amount) || 0);
                return;
            }
            openEditTransactionModal(row.dataset.id, row.dataset.date);
        });
    });
}

function removeCheckingTransferMirror(tx, origin) {
    if (!tx?.transferId) return;
    if (origin === 'personal' && tx.savingsTransfer) {
        const savingsMirror = (state.savingsTransactions || []).find(item => item.transferId === tx.transferId);
        if (savingsMirror) savingsMirror.personalMirrorDetached = true;
        return;
    }
    if (origin === 'personal') {
        const index = state.jointRegister.findIndex(item => item.transferId === tx.transferId);
        if (index > -1) state.jointRegister.splice(index, 1);
    } else {
        Object.values(state.personalCalendar || {}).forEach(list => {
            const index = list.findIndex(item => item.transferId === tx.transferId);
            if (index > -1) list.splice(index, 1);
        });
    }
}

function syncCheckingTransferMirror(tx, origin) {
    if (!tx?.transferId) return;
    if (origin === 'personal' && tx.savingsTransfer) {
        const savingsMirror = (state.savingsTransactions || []).find(item => item.transferId === tx.transferId);
        if (savingsMirror) {
            savingsMirror.date = tx.date;
            savingsMirror.description = tx.description;
            savingsMirror.amount = -Number(tx.amount || 0);
        }
        return;
    }
    if (origin === 'personal') {
        const mirror = state.jointRegister.find(item => item.transferId === tx.transferId);
        if (mirror) {
            mirror.date = tx.date;
            mirror.name = tx.description;
            mirror.amount = -Number(tx.amount || 0);
            mirror.jason = mirror.amount;
            mirror.asia = 0;
            mirror.type = 'contribution';
        }
    } else {
        let mirror = null;
        Object.values(state.personalCalendar || {}).forEach(list => {
            const index = list.findIndex(item => item.transferId === tx.transferId);
            if (index > -1) mirror = list.splice(index, 1)[0];
        });
        const dateObj = new Date(tx.date + 'T00:00:00');
        const month = MONTH_ORDER[dateObj.getMonth()];
        const key = `${dateObj.getFullYear()}-${month}`;
        ensureYearMonthInitialized(dateObj.getFullYear(), month);
        mirror = mirror || { id: 'p-' + Math.random().toString(36).substr(2, 9), transferId: tx.transferId };
        mirror.date = tx.date;
        mirror.description = tx.name || tx.description;
        mirror.amount = -Number(tx.jason || 0);
        state.personalCalendar[key].push(mirror);
    }
}
function renderJointList() {
    const container = document.getElementById('list-view-table-container');
    const periodLabel = state.listScope === 'month' ? `${MONTH_NAMES[state.currentMonth]} ${state.currentYear}` : String(state.currentYear);
    document.getElementById('list-view-title').textContent = `Joint Account Ledger (${periodLabel})`;
    const periodStart = state.listScope === 'month' ? `${state.currentYear}-${String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0')}-01` : `${state.currentYear}-01-01`;
    const periodEnd = state.listScope === 'month' ? `${state.currentYear}-${String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0')}-${String(new Date(state.currentYear, MONTH_ORDER.indexOf(state.currentMonth) + 1, 0).getDate()).padStart(2, '0')}` : `${state.currentYear}-12-31`;
    const year = parseInt(periodStart.slice(0, 4));
    const monthsToLoad = state.listScope === 'month' ? [state.currentMonth] : MONTH_ORDER;
    const dynamicTxs = [];
    monthsToLoad.forEach(m => {
        const mIdx = MONTH_ORDER.indexOf(m);
        const mPart = String(mIdx + 1).padStart(2, '0');

        // Jason's side uses the same balance-adjusted amount the calendar view shows (including
        // any insufficient-funds reduction) so this list doesn't show a different figure than the
        // calendar for the same real-world transfer. Asia's side has no such adjustment anywhere
        // in the app, so it stays on the raw calculated amount.
        const monthAdjustedTransfers = getAdjustedTransferAmountsForMonth(year, m);

        const addDynamicContributions = (cycle, date) => {
            if (date < periodStart || date > periodEnd) return;

            const jasonAdj = monthAdjustedTransfers[`xfer-${cycle}-${year}-${m}`];
            const definitions = [
                {
                    id: `joint-xfer-jason-${cycle}-${year}-${m}`,
                    person: 'jason',
                    description: 'Jason Joint Contribution (Dynamic)',
                    calculatedAmount: jasonAdj ? jasonAdj.amount : 0
                },
                {
                    id: `joint-xfer-asia-${cycle}-${year}-${m}`,
                    person: 'asia',
                    description: 'Asia Joint Contribution (Dynamic)',
                    calculatedAmount: getCalculatedTransferForAsia(year, m, cycle)
                }
            ];

            definitions.forEach(definition => {
                const override = (state.dynamicOverrides || {})[definition.id];
                if (override?.deleted) return;

                const amount = override?.amount !== undefined
                    ? Math.abs(Number(override.amount) || 0)
                    : definition.calculatedAmount;
                if (amount === 0) return;

                dynamicTxs.push({
                    id: definition.id,
                    date,
                    type: 'contribution',
                    name: override?.description || definition.description,
                    jason: definition.person === 'jason' ? amount : 0,
                    asia: definition.person === 'asia' ? amount : 0,
                    amount,
                    isSplitterDynamic: true
                });
            });
        };

        addDynamicContributions('1st', `${year}-${mPart}-01`);
        addDynamicContributions('15th', `${year}-${mPart}-15`);
    });

    const register = [...state.jointRegister]
        .filter(tx => tx.date >= periodStart && tx.date <= periodEnd && !tx.billOccurrenceDeleted && !(tx.type === 'contribution' && !tx.transferId))
        .concat(dynamicTxs)
        .sort((a, b) => a.date.localeCompare(b.date) || String(a.id).localeCompare(String(b.id)));

    const contributions = register.filter(tx => tx.type === 'contribution');
    const jasonTotal = contributions.reduce((sum, tx) => sum + (Number(tx.jason) || 0), 0);
    const asiaTotal = contributions.reduce((sum, tx) => sum + (Number(tx.asia) || 0), 0);
    const contributionTotal = jasonTotal + asiaTotal;
    
    // First compute running balance chronologically
    let runningVal = getJointRunningBalanceAtDate(periodStart);
    register.forEach(tx => {
        runningVal += Number(tx.amount) || 0;
        tx.runningBalance = runningVal;
    });

    // Apply cycle filter (only in Month view)
    let filteredRegister = register;
    if (state.listScope === 'month') {
        const cycleFilter = state.listCycleFilter || 'all';
        if (cycleFilter === '1st') {
            filteredRegister = register.filter(t => parseInt(t.date.split('-')[2]) < 15);
        } else if (cycleFilter === '2nd') {
            filteredRegister = register.filter(t => parseInt(t.date.split('-')[2]) >= 15);
        }
    }

    // Sort based on user preference
    const sortedRegister = sortTransactions(filteredRegister, state.listSort);

    const money = amount => `${amount < 0 ? '-' : '+'}$${Math.abs(amount).toFixed(2)}`;
    const color = amount => amount < 0 ? 'negative' : 'positive';

    let rows = '';
    sortedRegister.forEach(tx => {
        const description = tx.name || tx.description || 'Transaction';
        const deleteBtn = tx.isSplitterDynamic
            ? `<button class="action-btn small-btn danger-btn hide-dynamic-joint-btn" data-id="${tx.id}" data-date="${tx.date}" data-desc="${escapeHTML(description)}">Delete</button>`
            : `<button class="action-btn small-btn danger-btn delete-joint-btn" data-id="${tx.id}">Delete</button>`;
        rows += `<tr class="editable-row" data-id="${tx.id}" data-date="${tx.date}" data-desc="${escapeHTML(description)}" data-amount="${tx.amount}" data-dynamic="${tx.isSplitterDynamic ? 'true' : 'false'}" style="cursor:pointer;">
            <td>${tx.date}</td><td><strong>${escapeHTML(description)}</strong> ${getTransactionIndicatorBadges(tx)}</td>
            <td class="${color(Number(tx.jason) || 0)}">${tx.type === 'contribution' ? money(Number(tx.jason) || 0) : '—'}</td>
            <td class="${color(Number(tx.asia) || 0)}">${tx.type === 'contribution' ? money(Number(tx.asia) || 0) : '—'}</td>
            <td class="${color(Number(tx.amount) || 0)} font-heading">${money(Number(tx.amount) || 0)}</td>
            <td class="${color(tx.runningBalance)} font-heading">$${tx.runningBalance.toFixed(2)}</td>
            <td class="table-actions-cell">${deleteBtn}</td></tr>`;
    });
    if (!rows) rows = '<tr><td colspan="7" class="muted-text" style="text-align:center;padding:2rem;">No joint transactions logged for this period.</td></tr>';

    const getSortCaret = (colKey) => {
        if (state.listSort.key === colKey) {
            return state.listSort.direction === 'asc' ? ' ▲' : ' ▼';
        }
        return '';
    };

    container.innerHTML = `<div class="glass-card" style="padding:1rem;margin-bottom:1rem;"><div style="display:flex;gap:2rem;flex-wrap:wrap;"><span>Jason Contributions: <strong class="${color(jasonTotal)}">${money(jasonTotal)}</strong></span><span>Asia Contributions: <strong class="${color(asiaTotal)}">${money(asiaTotal)}</strong></span><span>Total Contributions: <strong class="${color(contributionTotal)}">${money(contributionTotal)}</strong></span></div></div>
        <div class="table-responsive">
            <table class="data-table">
                <thead>
                    <tr>
                        <th style="cursor:pointer;" onclick="toggleListSort('date')">Date${getSortCaret('date')}</th>
                        <th style="cursor:pointer;" onclick="toggleListSort('description')">Description${getSortCaret('description')}</th>
                        <th style="cursor:pointer;" onclick="toggleListSort('jason')">Jason${getSortCaret('jason')}</th>
                        <th style="cursor:pointer;" onclick="toggleListSort('asia')">Asia${getSortCaret('asia')}</th>
                        <th style="cursor:pointer;" onclick="toggleListSort('amount')">Debit / Credit${getSortCaret('amount')}</th>
                        <th style="cursor:pointer;" onclick="toggleListSort('runningBalance')">Running Balance${getSortCaret('runningBalance')}</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>${rows}</tbody>
            </table>
        </div>`;

    container.querySelectorAll('.delete-joint-btn').forEach(button => button.addEventListener('click', event => {
        event.stopPropagation();
        const index = state.jointRegister.findIndex(tx => tx.id === event.currentTarget.dataset.id);
        if (index < 0) return;
        const target = state.jointRegister[index];
        if (target.isAutomaticCardPayment) {
            alert('Automatic card payments cannot be deleted from the ledger. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
            return;
        }
        if (target.linkedBillId) {
            // Bill-generated occurrence: flag instead of splicing, or the sync regenerates it.
            target.billOccurrenceDate = target.billOccurrenceDate || target.date;
            target.billOccurrenceDeleted = true;
            saveDatabase();
            renderApp();
            logSystem(`Deleted bill occurrence: ${target.name || target.description} on ${target.date} (bill setting unchanged)`);
            return;
        }
        const removed = state.jointRegister.splice(index, 1)[0];
        if (removed.transferId) Object.values(state.personalCalendar || {}).forEach(list => {
            const mirrorIndex = list.findIndex(tx => tx.transferId === removed.transferId);
            if (mirrorIndex > -1) list.splice(mirrorIndex, 1);
        });
        removeLinkedCardPaymentLeg(removed);
        saveDatabase();
        renderApp();
        logSystem(`Deleted joint transaction: ${removed.name || removed.description}`);
    }));
    container.querySelectorAll('.hide-dynamic-joint-btn').forEach(button => button.addEventListener('click', event => {
        event.stopPropagation();
        const { id, date, desc } = event.currentTarget.dataset;
        const linkedMessage = getLinkedDynamicTxId(id) ? ' The matching personal transfer will also be hidden.' : '';
        if (!confirm(`Are you sure you want to hide "${desc}" on ${date}?${linkedMessage}`)) return;

        saveDynamicTxOverride(id, { deleted: true });
        saveDatabase();
        renderApp();
        logSystem(`Hidden dynamic joint contribution ${id} on ${date}`);
    }));

    container.querySelectorAll('.editable-row').forEach(row => row.addEventListener('dblclick', () => {
        if (row.dataset.dynamic === 'true') {
            openDynamicTxEditor(row.dataset.id, row.dataset.date, row.dataset.desc, parseFloat(row.dataset.amount) || 0);
            return;
        }
        openEditTransactionModal(row.dataset.id, row.dataset.date);
    }));
}
function showDayHighlightsDialog(sourceId) {
    const source = document.getElementById(sourceId);
    const content = document.getElementById('day-highlights-dialog-content');
    content.replaceChildren(...Array.from(source.childNodes));
    document.getElementById('day-highlights-dialog').showModal();
}

function renderDayHighlights(day) {
    const list = document.getElementById('today-highlights-list');
    list.innerHTML = '';
    
    const formattedDate = new Date(day.date + 'T00:00:00').toLocaleDateString('en-US', {
        weekday: 'long', year: 'numeric', month: 'long', day: 'numeric'
    });
    
    const headerHtml = `
        <div style="margin-bottom: 0.5rem;">
            <strong>${formattedDate}</strong>
            <div style="font-size: 0.85rem; color: var(--text-secondary); margin-top: 2px;">End of Day Balance: $${day.balance.toFixed(2)}</div>
        </div>
    `;
    list.insertAdjacentHTML('beforeend', headerHtml);
    
    if (day.transactions.length === 0) {
        list.insertAdjacentHTML('beforeend', `<p class="muted-text">No transactions logged for this day.</p>`);
        return;
    }
    
    day.transactions.forEach(t => {
        const highlightClass = t.type;
        const prefix = t.amount >= 0 ? '+' : '';
        const itemHtml = document.createElement('div');
        itemHtml.className = 'highlight-item';
        
        const isDynamicXfer = isDynamicTxId(t.id);
        const isDeletable = true;
        
        itemHtml.style.cursor = 'pointer';
        itemHtml.title = 'Double-click to edit/delete';
        
        itemHtml.innerHTML = `
            <div class="highlight-item-left">
                <span class="highlight-item-title">${escapeHTML(t.description)}${getTransactionIndicatorBadges(t)}</span>
                <span class="highlight-item-tag">${t.type.toUpperCase()}</span>
            </div>
            <div style="display: flex; align-items: center; gap: 0.75rem;">
                <span class="highlight-item-amount ${highlightClass}">${prefix}$${t.amount.toFixed(2)}</span>
                ${isDeletable ? `<button class="action-btn small-btn danger-btn delete-tx-btn" data-date="${day.date}" data-desc="${escapeHTML(t.description)}" data-amt="${t.amount}" data-isgig="${t.isGig ? 'true' : 'false'}" data-id="${t.id}" data-dynamic="${isDynamicXfer ? 'true' : 'false'}">Delete</button>` : ''}
            </div>
        `;
        
        itemHtml.addEventListener('dblclick', () => {
            if (t.id && t.id.startsWith('dynamic-delivery-')) {
                const modal = document.getElementById('day-highlights-dialog');
                if (modal && modal.open) modal.close();
                switchToTab('delivery');
                return;
            }
            if (t.isGig) {
                if (confirm(`Would you like to delete the side gig log for ${day.date}?`)) {
                    state.deliveryEarnings = state.deliveryEarnings.filter(g => g.date !== day.date);
                    saveDatabase();
                    renderApp();
                    logSystem(`Deleted side gig entry on ${day.date}`);
                    if (window.activeCalendarDays) {
                        const updatedDay = window.activeCalendarDays.find(d => d.date === day.date);
                        if (updatedDay) renderDayHighlights(updatedDay);
                    }
                }
                return;
            }

            if (isDynamicXfer) {
                openDynamicTxEditor(t.id, day.date, t.description, t.amount);
                return;
            }
            openEditTransactionModal(t.id, day.date);
        });
        
        const delBtn = itemHtml.querySelector('.delete-tx-btn');
        if (delBtn) {
            delBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                const dDate = e.target.dataset.date;
                const dDesc = e.target.dataset.desc;
                const dAmt = parseFloat(e.target.dataset.amt);
                const isGig = e.target.dataset.isgig === 'true';
                const txId = e.target.dataset.id;
                const isDynamic = e.target.dataset.dynamic === 'true';
                
                if (isGig) {
                    if (confirm(`Are you sure you want to delete the side gig log for ${dDate}?`)) {
                        state.deliveryEarnings = state.deliveryEarnings.filter(g => g.date !== dDate);
                        saveDatabase();
                        renderApp();
                        logSystem(`Deleted side gig entry on ${dDate}`);
                        if (window.activeCalendarDays) {
                            const updatedDay = window.activeCalendarDays.find(d => d.date === dDate);
                            if (updatedDay) renderDayHighlights(updatedDay);
                        }
                    }
                    return;
                }

                // Dynamic xfer/contribution delete – store override, don't touch bill splitter
                if (isDynamic) {
                    const settingLabel = String(txId).startsWith('dynamic-paycheck-') ? 'payroll schedule' : 'bill splitter settings';
                    if (confirm(`Are you sure you want to hide "${dDesc}" on ${dDate}? This does not change your ${settingLabel}.`)) {
                        saveDynamicTxOverride(txId, { deleted: true });
                        saveDatabase();
                        renderApp();
                        logSystem(`Hidden dynamic transaction ${txId} on ${dDate}`);
                        if (window.activeCalendarDays) {
                            const updatedDay = window.activeCalendarDays.find(d => d.date === dDate);
                            if (updatedDay) renderDayHighlights(updatedDay);
                        }
                    }
                    return;
                }
                
                if (confirm(`Are you sure you want to delete "${dDesc}" on ${dDate}?`)) {
                    if (state.dashboardType === 'personal') {
                        const monthObj = new Date(dDate + 'T00:00:00');
                        const key = `${monthObj.getFullYear()}-${MONTH_ORDER[monthObj.getMonth()]}`;
                        const txList = state.personalCalendar[key] || [];
                        
                        const index = txList.findIndex(tx => tx.id === txId || (tx.date === dDate && tx.description === dDesc && Math.abs(tx.amount - dAmt) < 0.01));
                        if (index > -1) {
                            const tx = txList[index];
                            if (tx.isAutomaticCardPayment) {
                                alert('Automatic card payments cannot be deleted from the ledger. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
                                return;
                            }
                            if (tx.splitterItem) {
                                tx.billOccurrenceDeleted = true;
                                logSystem(`Deleted splitter item occurrence on ${dDate}: ${dDesc}`);
                            } else {
                                const removed = txList.splice(index, 1)[0];
                                removeCheckingTransferMirror(removed, 'personal');
                                removeLinkedCardPaymentLeg(removed);
                                logSystem(`Deleted personal transaction on ${dDate}: ${dDesc} ($${dAmt.toFixed(2)})`);
                            }
                            saveDatabase();
                            renderApp();
                        }
                    } else if (state.dashboardType === 'joint') {
                        const index = state.jointRegister.findIndex(tx => tx.id === txId || (tx.date === dDate && tx.name === dDesc && Math.abs(tx.amount - dAmt) < 0.01));
                        if (index > -1) {
                            const tx = state.jointRegister[index];
                            if (tx.isAutomaticCardPayment) {
                                alert('Automatic card payments cannot be deleted from the ledger. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
                                return;
                            }
                            if (tx.splitterItem) {
                                tx.billOccurrenceDeleted = true;
                                logSystem(`Deleted splitter item occurrence on ${dDate}: ${dDesc}`);
                            } else {
                                const removed = state.jointRegister.splice(index, 1)[0];
                                removeCheckingTransferMirror(removed, 'joint');
                                removeLinkedCardPaymentLeg(removed);
                                logSystem(`Deleted joint transaction on ${dDate}: ${dDesc} ($${dAmt.toFixed(2)})`);
                            }
                            saveDatabase();
                            renderApp();
                        }
                    } else {
                        // Credit Card delete
                        const cardId = state.dashboardType;
                        const dateObj = new Date(dDate + 'T00:00:00');
                        const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
                        const list = (state.cardCalendars && state.cardCalendars[cardId]) ? (state.cardCalendars[cardId][key] || []) : [];
                        const index = list.findIndex(tx => tx.id === txId || (tx.date === dDate && tx.description === dDesc && Math.abs(tx.amount - dAmt) < 0.01));
                        if (index > -1) {
                            deleteCardTransactionWithRecurringChoice(cardId, key, list[index].id);
                            saveDatabase();
                            renderApp();
                            logSystem(`Deleted credit card transaction on ${dDate}: ${dDesc}`);
                        }
                    }
                    
                    if (window.activeCalendarDays) {
                        const updatedDay = window.activeCalendarDays.find(d => d.date === dDate);
                        if (updatedDay) renderDayHighlights(updatedDay);
                    }
                }
            });
        }
        list.appendChild(itemHtml);
    });
}

// 3. RENDER BILLS SPLITTER TAB (1st & 15th split calculator)
function resetBillSplitterForm() {
    document.getElementById('joint-bill-form').reset();
    document.getElementById('bill-edit-id').value = '';
    document.getElementById('bill-edit-cycle').value = '';
    document.getElementById('bill-modal-title').textContent = 'Add Bill Splitter Item';
    document.getElementById('btn-save-bill').textContent = 'Save Item';
    document.getElementById('bill-same-payment').checked = true;
    document.getElementById('bill-entry-type').value = 'actual';
    document.getElementById('bill-category').value = 'bill';
    document.getElementById('bill-budget-frequency').value = 'monthly';
    document.getElementById('bill-charge-frequency').value = 'monthly';
    document.getElementById('bill-weekly-day').value = '6';
    document.getElementById('bill-weekly-day-group').classList.add('hidden');
    document.getElementById('bill-frequency-start-group').classList.add('hidden');
    document.getElementById('bill-budget-amount-label').textContent = 'Transfer Amount';
    document.getElementById('bill-budget-preview').textContent = '';
    const currentMonthNumber = String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0');
    document.getElementById('bill-recurring-start').value = `${state.currentYear}-${currentMonthNumber}-01`;
    document.getElementById('bill-frequency-start').value = `${state.currentYear}-${currentMonthNumber}-01`;
    document.getElementById('bill-recurring-end').value = '';
    document.getElementById('bill-recurrence-dates-group').classList.add('hidden');
    document.getElementById('bill-payment-source-group').classList.remove('hidden');
    document.getElementById('bill-due-day-group').classList.remove('hidden');
    document.getElementById('bill-due-day').required = true;
    document.getElementById('bill-payment-amount-group').classList.add('hidden');

    const warning = document.getElementById('mortgage-bill-warning');
    if (warning) warning.classList.add('hidden');
    const form = document.getElementById('joint-bill-form');
    if (form) {
        form.querySelectorAll('input, select, button').forEach(el => el.disabled = false);
    }
}

function openBillSplitterEditor(bill, cycleKey) {
    populateCCDropdowns();
    document.getElementById('bill-edit-id').value = bill.id;
    document.getElementById('bill-edit-cycle').value = cycleKey;
    document.getElementById('bill-modal-title').textContent = 'Edit Bill Splitter Item';
    document.getElementById('btn-save-bill').textContent = 'Update Item';
    document.getElementById('bill-name').value = bill.account;
    document.getElementById('bill-entry-type').value = bill.entryType;
    document.getElementById('bill-category').value = bill.category || 'bill';
    document.getElementById('bill-ownership').value = bill.ownership;
    document.getElementById('bill-cycle').value = bill.cycleAllocation || (cycleKey === 'cycle1st' ? '1st' : '15th');
    document.getElementById('bill-due-day').value = bill.dueDay;
    document.getElementById('bill-payment-source').value = bill.paymentSource;
    document.getElementById('bill-recurring').checked = bill.isRecurring;
    // The start field is a full date now; legacy bills that only stored recurringStartMonth display
    // as that month's first day.
    document.getElementById('bill-recurring-start').value = bill.recurringStartDate || (bill.recurringStartMonth ? `${bill.recurringStartMonth}-01` : '');
    // The end field is a full date now; legacy bills that only stored recurringEndMonth display as
    // that month's last day.
    document.getElementById('bill-recurring-end').value = bill.recurringEndDate
        || (bill.recurringEndMonth
            ? (() => { const [y, m] = bill.recurringEndMonth.split('-').map(Number); return `${bill.recurringEndMonth}-${String(new Date(y, m, 0).getDate()).padStart(2, '0')}`; })()
            : '');
    document.getElementById('bill-recurrence-dates-group').classList.toggle('hidden', !bill.isRecurring);
    document.getElementById('bill-budget-frequency').value = bill.budgetFrequency || 'monthly';
    document.getElementById('bill-charge-frequency').value = bill.chargeFrequency || 'monthly';
    document.getElementById('bill-weekly-day').value = String(bill.weeklyDay ?? 6);
    document.getElementById('bill-frequency-start').value = bill.frequencyStartDate || '';
    document.getElementById('bill-amount-field').value = bill.frequencyAmount;
    document.getElementById('bill-weekly-day-group').classList.add('hidden');
    document.getElementById('bill-frequency-start-group').classList.toggle('hidden', bill.chargeFrequency === 'monthly');
    document.getElementById('bill-budget-amount-label').textContent = 'Transfer Amount';
    document.getElementById('bill-budget-preview').textContent = `${bill.weeklyOccurrences} scheduled charge${bill.weeklyOccurrences === 1 ? '' : 's'}; transfer budget $${bill.budgetAmount.toFixed(2)} for ${MONTH_NAMES[state.currentMonth]}`;
    document.getElementById('bill-same-payment').checked = bill.samePaymentAmount;
    document.getElementById('bill-payment-amount').value = bill.occurrencePaymentAmount;
    document.getElementById('bill-payment-source-group').classList.toggle('hidden', bill.entryType !== 'actual');
    document.getElementById('bill-due-day-group').classList.toggle('hidden', bill.entryType !== 'actual' || bill.chargeFrequency !== 'monthly');
    document.getElementById('bill-due-day').required = bill.entryType === 'actual' && bill.chargeFrequency === 'monthly';
    document.getElementById('bill-payment-amount-group').classList.toggle('hidden', bill.samePaymentAmount || bill.entryType !== 'actual');
    document.getElementById('bill-ownership').dispatchEvent(new Event('change'));

    const isMortgage = !!bill.isMortgage;
    const isOverrideActive = isMortgage && !!bill.isMortgageOverrideActive;
    const warning = document.getElementById('mortgage-bill-warning');
    if (warning) warning.classList.toggle('hidden', !isMortgage);
    
    const isBillTrackerSynced = !!bill.billTrackerSettingId;
    const trackerWarning = document.getElementById('billtracker-bill-warning');
    if (trackerWarning) trackerWarning.classList.toggle('hidden', !isBillTrackerSynced);

    const isCardPayment = !!bill.linkedCardPaymentId;
    const isAutoCardPayment = isCardPayment && bill.cardPaymentKind === 'auto';
    const paymentTargetAccount = isCardPayment && bill.payoffTargetId ? state.loans.find(l => l.id === bill.payoffTargetId) : null;
    const isLoanTarget = paymentTargetAccount && paymentTargetAccount.type === 'loan';
    const paymentAccountLabel = isLoanTarget ? 'loan' : 'credit card';
    const cardPaymentWarning = document.getElementById('card-payment-bill-warning');
    if (cardPaymentWarning) {
        cardPaymentWarning.classList.toggle('hidden', !isCardPayment);
        const warningText = document.getElementById('card-payment-bill-warning-text');
        if (warningText) {
            warningText.textContent = isAutoCardPayment
                ? `This entry is synchronized from an automatic ${paymentAccountLabel} payment. Only the budget fields (budget method, transfer amount, same-payment toggle) can be edited here. To change the payment itself, adjust the ${paymentAccountLabel}’s payment strategy in`
                : `This entry is synchronized from a scheduled ${paymentAccountLabel} payment. To change or delete it, edit the payment itself in`;
        }
        const cardPaymentLink = document.getElementById('link-to-card-payment');
        if (cardPaymentLink) cardPaymentLink.textContent = isLoanTarget ? 'Installment Loans' : 'Credit Cards';
    }

    const form = document.getElementById('joint-bill-form');
    if (form) {
        form.querySelectorAll('input, select, button').forEach(el => {
            // bill-due-day's disabled state is already correctly set by updateBillFormVisibility
            // (dispatched just above) based on entry type/frequency — it must not be blindly
            // re-enabled here, since its value is stored as 0 for inapplicable bills and fails the
            // field's min="1" constraint, silently blocking native form submission when enabled.
            if (el.id === 'bill-due-day') return;
            if (el.id === 'btn-cancel-bill' || el.id === 'link-to-mortgage-settings' || el.id === 'link-to-bill-tracker-settings' || el.id === 'link-to-card-payment') {
                el.disabled = false;
            } else if (isCardPayment) {
                // The transfer cycle (1st / 15th / both) is always editable for dynamic card/loan
                // payment rows, even manual ones whose amount and date stay locked to Credit Cards/Loans.
                const allowedIds = isAutoCardPayment
                    ? ['bill-budget-frequency', 'bill-amount-field', 'bill-same-payment', 'bill-cycle', 'btn-save-bill']
                    : ['bill-cycle', 'btn-save-bill'];
                el.disabled = !allowedIds.includes(el.id);
            } else if (isMortgage) {
                const allowedIds = ['bill-budget-frequency', 'btn-save-bill'];
                if (!isOverrideActive) {
                    allowedIds.push('bill-amount-field', 'bill-same-payment');
                }
                el.disabled = !allowedIds.includes(el.id);
            } else if (isBillTrackerSynced) {
                const allowedIds = ['bill-budget-frequency', 'bill-amount-field', 'bill-same-payment', 'bill-payment-amount', 'btn-save-bill'];
                el.disabled = !allowedIds.includes(el.id);
            } else {
                el.disabled = false;
            }
        });
    }

    if (isCardPayment) {
        const cardLink = document.getElementById('link-to-card-payment');
        if (cardLink) {
            cardLink.onclick = (e) => {
                e.preventDefault();
                goToCardPaymentInCreditCards(bill.payoffTargetId, bill.linkedPaymentDate);
            };
        }
    }

    if (isMortgage) {
        const link = document.getElementById('link-to-mortgage-settings');
        if (link) {
            link.onclick = (e) => {
                e.preventDefault();
                document.getElementById('joint-bill-dialog').close();
                switchToTab('loans');
                state.ccSelectedCardId = '';
                renderLoansTab();
                openEditLoanModal(bill.mortgageLoanId);
            };
        }
    }

    if (isBillTrackerSynced) {
        const link = document.getElementById('link-to-bill-tracker-settings');
        if (link) {
            link.onclick = (e) => {
                e.preventDefault();
                document.getElementById('joint-bill-dialog').close();
                switchToTab('billtracker');
                renderBillTrackerTab();
                openEditBillSettingModal(bill.billTrackerSettingId);
            };
        }
    }

    document.getElementById('joint-bill-dialog').showModal();
}
// Sums a person's allocation contributions for one cycle across both storage arrays, since 'both'
// (split 1st & 15th) allocations are stored once in cycle1st.contributions but contribute half to
// each cycle's total — mirroring how 'both'-cycle bills are already split in cycle total math.
function getAllocationCycleTotal(mBills, cycleKey, person) {
    let total = 0;
    ['cycle1st', 'cycle15th'].forEach(ck => {
        (mBills[ck]?.contributions || []).forEach(item => {
            const amount = Number(item[person]) || 0;
            if (item.cycle === 'both') total += amount / 2;
            else if (ck === cycleKey) total += amount;
        });
    });
    return total;
}
function getAllocationOccurrenceCount(frequency, startDate, year, month, endDate = '') {
    const monthIndex = MONTH_ORDER.indexOf(month);
    if (monthIndex < 0) return 0;
    const first = new Date(Number(year), monthIndex, 1);
    const last = new Date(Number(year), monthIndex + 1, 0);
    const start = startDate ? new Date(`${startDate}T00:00:00`) : first;
    if (Number.isNaN(start.getTime()) || last < start) return 0;
    const end = endDate ? new Date(`${endDate}T00:00:00`) : null;
    if (end && !Number.isNaN(end.getTime()) && first > end) return 0;
    if (frequency === 'yearly') return first.getMonth() === start.getMonth() && first.getFullYear() >= start.getFullYear() ? 1 : 0;
    if (frequency !== 'weekly') return 1;
    let count = 0;
    for (let day = 1; day <= last.getDate(); day++) {
        const date = new Date(Number(year), monthIndex, day);
        if (end && !Number.isNaN(end.getTime()) && date > end) break;
        if (date >= start && date.getDay() === start.getDay()) count++;
    }
    return count;
}function updateFutureAllocationOccurrences(seriesId, role, year, month, changes) {
    const currentIndex = year * 12 + MONTH_ORDER.indexOf(month);
    Object.entries(state.monthlyBills || {}).forEach(([key, monthData]) => {
        const [keyYear, keyMonth] = key.split('-');
        const periodIndex = Number(keyYear) * 12 + MONTH_ORDER.indexOf(keyMonth);
        if (periodIndex <= currentIndex) return;
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            monthData[cycleKey].contributions = (monthData[cycleKey].contributions || []).filter(item => item.seriesId !== seriesId || (role !== 'base' && (item.role || 'base') !== role));
        });
        applyAllocationTemplatesForMonth(Number(keyYear), keyMonth);
        recalculateBillCycleTotals(monthData);
    });
}function deleteAllocationOccurrence(allocation, year, month, deleteFuture) {
    const seriesId = allocation.seriesId || '';
    const role = allocation.role || 'base';
    const currentIndex = year * 12 + MONTH_ORDER.indexOf(month);
    const legacyName = String(allocation.name || '').trim().toLowerCase();
    const recurrenceKey = seriesId ? `${seriesId}|${role}` : '';
    let removed = 0;
    if (seriesId) {
        if (deleteFuture) state.allocationRecurrenceStops[recurrenceKey] = currentIndex;
        else state.allocationRecurrenceSkips[`${recurrenceKey}|${year}-${month}`] = true;
    }
    Object.entries(state.monthlyBills || {}).forEach(([key, monthData]) => {
        const [keyYear, keyMonth] = key.split('-');
        const periodIndex = Number(keyYear) * 12 + MONTH_ORDER.indexOf(keyMonth);
        if (!deleteFuture && key !== `${year}-${month}`) return;
        if (deleteFuture && periodIndex < currentIndex) return;
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            const before = monthData[cycleKey].contributions.length;
            monthData[cycleKey].contributions = monthData[cycleKey].contributions.filter(item => {
                const sameSeries = seriesId && item.seriesId === seriesId && (item.role || 'base') === role;
                const sameLegacy = !seriesId && (item.role || 'base') === role && String(item.name || '').trim().toLowerCase() === legacyName;
                const selectedCurrentItem = !deleteFuture && key === `${year}-${month}` && item.id === allocation.id;
                return !(sameSeries || (deleteFuture && sameLegacy) || selectedCurrentItem);
            });
            removed += before - monthData[cycleKey].contributions.length;
        });
        recalculateBillCycleTotals(monthData);
    });
    return removed;
}
function applyAllocationTemplatesForMonth(year, month) {
    const key = `${year}-${month}`;
    const mBills = state.monthlyBills?.[key];
    if (!mBills) return;
    const targetIndex = year * 12 + MONTH_ORDER.indexOf(month);
    Object.values(state.allocationTemplates || {}).forEach(template => {
        if (targetIndex <= Number(template.startIndex)) return;
        const baseCycleKey = template.cycle === '15th' ? 'cycle15th' : 'cycle1st';
        const offsetCycleKey = template.cycle === '15th' ? 'cycle1st' : 'cycle15th';
        const hasRole = role => ['cycle1st','cycle15th'].some(cycleKey => (mBills[cycleKey].contributions || []).some(item => item.seriesId === template.seriesId && (item.role || 'base') === role));
        const canGenerate = role => {
            const recurrenceKey = `${template.seriesId}|${role}`;
            const stoppedAt = state.allocationRecurrenceStops?.[recurrenceKey];
            const skipped = state.allocationRecurrenceSkips?.[`${recurrenceKey}|${key}`];
            return !skipped && !(Number.isFinite(Number(stoppedAt)) && Number(stoppedAt) <= targetIndex);
        };
        const occurrenceCount = getAllocationOccurrenceCount(template.frequency || 'monthly', template.startDate || '', year, month, template.endDate || '');
        const templateAmount = value => value === null || value === undefined || value === ''
            ? null
            : (template.signedValues ? Number(value) : -Math.abs(Number(value))) * occurrenceCount;
        if (occurrenceCount > 0 && !hasRole('base') && canGenerate('base')) mBills[baseCycleKey].contributions.push({ id: `alloc-${template.seriesId}-${year}-${month}-base`, seriesId: template.seriesId, role: 'base', name: template.name, jason: templateAmount(template.jason), asia: templateAmount(template.asia), sourceJason: template.jason, sourceAsia: template.asia, cycle: template.cycle, frequency: template.frequency || 'monthly', startDate: template.startDate || '', occurrenceCount });
        if (occurrenceCount > 0 && template.offsetEnabled && !hasRole('offset') && canGenerate('offset')) mBills[offsetCycleKey].contributions.push({ id: `alloc-${template.seriesId}-${year}-${month}-offset`, seriesId: template.seriesId, role: 'offset', name: template.name, jason: templateAmount(template.offsetJason), asia: templateAmount(template.offsetAsia), sourceJason: template.offsetJason, sourceAsia: template.offsetAsia, cycle: template.cycle === '15th' ? '1st' : '15th', frequency: template.frequency || 'monthly', startDate: template.startDate || '', occurrenceCount });
    });
}
function openAllocationEditor(allocation, cycleKey) {
    document.getElementById('allocation-form').reset();
    document.getElementById('allocation-modal-title').textContent = 'Edit Personal Allocation';
    document.getElementById('alloc-edit-id').value = allocation.id;
    document.getElementById('alloc-edit-cycle').value = cycleKey;
    document.getElementById('alloc-name').value = allocation.name;
    document.getElementById('alloc-cycle').value = allocation.cycle === 'both' ? 'both' : (cycleKey === 'cycle15th' ? '15th' : '1st');
    const jasonAmount = allocation.sourceJason ?? allocation.jason;
    const asiaAmount = allocation.sourceAsia ?? allocation.asia;
    const hasJason = jasonAmount !== null && jasonAmount !== undefined && jasonAmount !== '';
    const hasAsia = asiaAmount !== null && asiaAmount !== undefined && asiaAmount !== '';
    document.getElementById('alloc-jason-enabled').checked = hasJason;
    document.getElementById('alloc-asia-enabled').checked = hasAsia;
    document.getElementById('alloc-jason-group').classList.toggle('hidden', !hasJason);
    document.getElementById('alloc-asia-group').classList.toggle('hidden', !hasAsia);
    document.getElementById('alloc-jason').value = hasJason ? jasonAmount : '';
    document.getElementById('alloc-asia').value = hasAsia ? asiaAmount : '';
    document.getElementById('alloc-frequency').value = allocation.frequency || 'monthly';
    document.getElementById('alloc-start-date').value = allocation.startDate || '';
    const occurrenceCount = getAllocationOccurrenceCount(allocation.frequency || 'monthly', allocation.startDate || '', state.currentYear, state.currentMonth);
    document.getElementById('alloc-frequency-preview').textContent = `${occurrenceCount} ${(allocation.frequency || 'monthly')} occurrence${occurrenceCount === 1 ? '' : 's'} in ${MONTH_NAMES[state.currentMonth]}.`;
    document.getElementById('alloc-offset-enabled').checked = false;
    document.getElementById('alloc-offset-fields').classList.add('hidden');
    const template = allocation.seriesId ? state.allocationTemplates[allocation.seriesId] : null;
    document.getElementById('alloc-recurring').checked = !!template;
    document.getElementById('alloc-recurrence-dates-group').classList.toggle('hidden', !template);
    document.getElementById('alloc-end-date').value = template ? (template.endDate || '') : '';
    document.getElementById('allocation-dialog').showModal();
}
// Adds `n` occurrences of `frequency` (yearly/quarterly/monthly) to `date`, preserving day-of-month
// where possible (clamped to the target month's length, e.g. Jan 31 + 1 month -> Feb 28/29).
function addSeasonalInterval(date, frequency, n) {
    const monthsToAdd = frequency === 'monthly' ? n : frequency === 'quarterly' ? n * 3 : n * 12;
    const day = date.getDate();
    const target = new Date(date.getFullYear(), date.getMonth() + monthsToAdd, 1);
    const daysInTarget = new Date(target.getFullYear(), target.getMonth() + 1, 0).getDate();
    target.setDate(Math.min(day, daysInTarget));
    return target;
}
// Generates one occurrence's semi-monthly installment dates going FORWARD from `occurrenceStart`
// (not backward from a one-time event like the old model) — the first installment lands on the
// nearest 1st/15th cycle on or after occurrenceStart, then alternates 1st/15th for up to `cycles`
// installments, stopping early if endDate is set and would be exceeded.
function getSeasonalFundingDates(expense, occurrenceStart) {
    const start = occurrenceStart || (expense.startDate ? new Date(expense.startDate + 'T00:00:00') : null);
    if (!start || Number.isNaN(start.getTime())) return [];
    const end = expense.endDate ? new Date(expense.endDate + 'T00:00:00') : null;
    let cursor;
    if (start.getDate() <= 1) cursor = new Date(start.getFullYear(), start.getMonth(), 1);
    else if (start.getDate() <= 15) cursor = new Date(start.getFullYear(), start.getMonth(), 15);
    else cursor = new Date(start.getFullYear(), start.getMonth() + 1, 1);
    const totalCycles = Math.max(1, Number(expense.cycles) || 1);
    const dates = [];
    while (dates.length < totalCycles) {
        if (end && cursor > end) break;
        dates.push(new Date(cursor));
        cursor = cursor.getDate() === 1 ? new Date(cursor.getFullYear(), cursor.getMonth(), 15) : new Date(cursor.getFullYear(), cursor.getMonth() + 1, 1);
    }
    return dates;
}
// A recurring expense's billing-cycle installments repeat every `frequency` interval anchored to
// startDate, in perpetuity (unless endDate stops it). Returns each occurrence's start date whose
// installments could plausibly land in (targetYear, targetMonthIndex).
function getSeasonalOccurrenceStarts(expense, targetYear, targetMonthIndex) {
    if (!expense.startDate) return [];
    const start = new Date(expense.startDate + 'T00:00:00');
    if (Number.isNaN(start.getTime())) return [];
    const end = expense.endDate ? new Date(expense.endDate + 'T00:00:00') : null;
    const targetMonthsFromEpoch = targetYear * 12 + targetMonthIndex;
    // Cycles alternate 1st/15th, so roughly cycles/2 months are spanned by one occurrence.
    const spanMonths = Math.ceil(Math.max(1, Number(expense.cycles) || 1) / 2) + 1;
    if (!expense.isRecurring) {
        const startMonthsFromEpoch = start.getFullYear() * 12 + start.getMonth();
        if (startMonthsFromEpoch > targetMonthsFromEpoch || startMonthsFromEpoch < targetMonthsFromEpoch - spanMonths) return [];
        return [start];
    }
    const frequency = expense.frequency || 'yearly';
    const starts = [];
    for (let n = 0; n < 5000; n++) {
        const occStart = addSeasonalInterval(start, frequency, n);
        if (end && occStart > end) break;
        const occMonthsFromEpoch = occStart.getFullYear() * 12 + occStart.getMonth();
        if (occMonthsFromEpoch > targetMonthsFromEpoch) break;
        if (occMonthsFromEpoch >= targetMonthsFromEpoch - spanMonths) starts.push(occStart);
    }
    return starts;
}
function removeSeasonalInstallments(expenseId) {
    Object.values(state.monthlyBills || {}).forEach(monthData => ['cycle1st','cycle15th'].forEach(cycleKey => { monthData[cycleKey].bills = (monthData[cycleKey].bills || []).filter(item => item.seasonalExpenseId !== expenseId); recalculateBillCycleTotals(monthData); }));
    Object.values(state.personalCalendar || {}).forEach(list => { for (let i = list.length - 1; i >= 0; i--) if (list[i].seasonalExpenseId === expenseId) list.splice(i, 1); });
    for (let i = state.jointRegister.length - 1; i >= 0; i--) if (state.jointRegister[i].seasonalExpenseId === expenseId) state.jointRegister.splice(i, 1);
}
function applySeasonalExpensesForMonth(year, month) {
    const mBills = state.monthlyBills?.[`${year}-${month}`]; if (!mBills) return;
    const monthIndex = MONTH_ORDER.indexOf(month);
    (state.seasonalExpenses || []).forEach(expense => getSeasonalOccurrenceStarts(expense, year, monthIndex).forEach(occStart => {
        getSeasonalFundingDates(expense, occStart).forEach(date => {
            if (date.getFullYear() !== year || date.getMonth() !== monthIndex) return;
            const cycleKey = date.getDate() === 15 ? 'cycle15th' : 'cycle1st'; const id = `${expense.id}-${formatLocalDate(date)}`;
            if (mBills[cycleKey].bills.some(item => item.id === id)) return;
            const totalCycles = Math.max(1, Number(expense.cycles) || 1);
            const installment = Math.round((expense.amount / totalCycles) * 100) / 100;
            mBills[cycleKey].bills.push(normalizeBillSplitterItem({ id, account: expense.name, category: 'expense', budgetAmount: installment, paymentAmount: 0, amount: -installment, dueDay: 0, entryType: 'calculation', ownership: 'joint', cycleAllocation: date.getDate() === 15 ? '15th' : '1st', seasonalExpenseId: expense.id, isRecurring: false }, cycleKey));
        });
    })); recalculateBillCycleTotals(mBills);
}
// The actual one-time charge (e.g. the $500 State Fair bill) posts as a real ledger transaction on
// its own chargeDate, independent of the Bill Splitter savings installments above, and repeats on
// the same yearly/quarterly/monthly cadence as the rest of the expense.
function getSeasonalChargeOccurrenceDate(expense, targetYear, targetMonthIndex) {
    if (!expense.hasCharge || !expense.chargeDate) return null;
    const chargeStart = new Date(expense.chargeDate + 'T00:00:00');
    if (Number.isNaN(chargeStart.getTime())) return null;
    const end = expense.endDate ? new Date(expense.endDate + 'T00:00:00') : null;
    const targetMonthsFromEpoch = targetYear * 12 + targetMonthIndex;
    if (!expense.isRecurring) {
        const startMonthsFromEpoch = chargeStart.getFullYear() * 12 + chargeStart.getMonth();
        return startMonthsFromEpoch === targetMonthsFromEpoch ? chargeStart : null;
    }
    const frequency = expense.frequency || 'yearly';
    for (let n = 0; n < 5000; n++) {
        const occ = addSeasonalInterval(chargeStart, frequency, n);
        if (end && occ > end) break;
        const occMonthsFromEpoch = occ.getFullYear() * 12 + occ.getMonth();
        if (occMonthsFromEpoch > targetMonthsFromEpoch) break;
        if (occMonthsFromEpoch === targetMonthsFromEpoch) return occ;
    }
    return null;
}
function applySeasonalChargeForMonth(year, month) {
    const monthIndex = MONTH_ORDER.indexOf(month);
    const key = `${year}-${month}`;
    (state.seasonalExpenses || []).forEach(expense => {
        const linkId = `seasonal-charge-${expense.id}-${year}-${String(monthIndex + 1).padStart(2, '0')}`;
        const occDate = expense.hasCharge ? getSeasonalChargeOccurrenceDate(expense, year, monthIndex) : null;
        const source = expense.chargeSource === 'joint' ? 'joint' : 'personal';
        const amount = occDate ? Math.max(0, Math.round((Number(expense.chargeAmount) || 0) * 100) / 100) : 0;
        const dateStr = occDate ? formatLocalDate(occDate) : null;

        const existingJoint = state.jointRegister.find(tx => tx.seasonalChargeId === linkId);
        const existingPersonal = Object.values(state.personalCalendar || {}).flat().find(tx => tx.seasonalChargeId === linkId);
        const existing = existingJoint || existingPersonal;
        if (existing && amount > 0 && existing.date === dateStr && Math.abs((Number(existing.amount) || 0) + amount) < 0.005
            && ((existingJoint && source === 'joint') || (existingPersonal && source === 'personal'))) return;

        Object.values(state.personalCalendar || {}).forEach(list => { for (let i = list.length - 1; i >= 0; i--) if (list[i].seasonalChargeId === linkId) list.splice(i, 1); });
        for (let i = state.jointRegister.length - 1; i >= 0; i--) if (state.jointRegister[i].seasonalChargeId === linkId) state.jointRegister.splice(i, 1);
        if (amount <= 0) return;

        const tx = { id: (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9), type: source === 'joint' ? 'expense' : undefined, name: expense.name, description: expense.name, date: dateStr, amount: -amount, seasonalChargeId: linkId, seasonalExpenseId: expense.id };
        ensureYearMonthInitialized(year, month);
        if (source === 'joint') state.jointRegister.push(tx);
        else { if (!state.personalCalendar[key]) state.personalCalendar[key] = []; state.personalCalendar[key].push(tx); }
    });
}
function openSeasonalEditor(expense) {
    document.getElementById('seasonal-modal-title').textContent = 'Edit Seasonal Expense'; document.getElementById('seasonal-edit-id').value = expense.id;
    document.getElementById('seasonal-name').value = expense.name; document.getElementById('seasonal-amount').value = expense.amount;
    document.getElementById('seasonal-cycles').value = expense.cycles;
    document.getElementById('seasonal-start-date').value = expense.startDate || '';
    document.getElementById('seasonal-end-date').value = expense.endDate || '';
    document.getElementById('seasonal-recurring').checked = !!expense.isRecurring;
    document.getElementById('seasonal-frequency').value = expense.frequency || 'yearly';
    document.getElementById('seasonal-frequency-group').classList.toggle('hidden', !expense.isRecurring);
    document.getElementById('seasonal-has-charge').checked = !!expense.hasCharge;
    document.getElementById('seasonal-charge-amount').value = expense.chargeAmount || '';
    document.getElementById('seasonal-charge-date').value = expense.chargeDate || '';
    document.getElementById('seasonal-charge-source').value = expense.chargeSource || 'personal';
    document.getElementById('seasonal-charge-group').classList.toggle('hidden', !expense.hasCharge);
    document.getElementById('seasonal-dialog').showModal();
}
function renderBillSplitterMetrics(mBills, allBills) {
    const ownership = state.billTrackerOwnership || 'joint';
    const metricCycle = state.billMetricsCycle || 'month';
    const selectedCycleLabel = metricCycle === 'month' ? 'Month' : metricCycle === '1st' ? '1st Cycle' : '15th Cycle';
    const allocateBillToCycle = (bill, cycle) => {
        if (bill.cycleAllocation === 'both') return bill.budgetAmount / 2;
        const billCycle = bill.cycleAllocation === '15th' ? '15th' : '1st';
        return billCycle === cycle ? bill.budgetAmount : 0;
    };
    const scopedBills = allBills.filter(bill => (bill.ownership || 'joint') === ownership);
    const expense1st = scopedBills.reduce((sum, bill) => sum + allocateBillToCycle(bill, '1st'), 0);
    const expense15th = scopedBills.reduce((sum, bill) => sum + allocateBillToCycle(bill, '15th'), 0);
    const expenseMonth = expense1st + expense15th;
    const allocationTotal = (person, cycle) => (mBills[cycle === '1st' ? 'cycle1st' : 'cycle15th']?.contributions || [])
        .reduce((sum, allocation) => sum + Math.abs(Number(allocation[person]) || 0), 0);
    const jason1st = allocationTotal('jason', '1st');
    const jason15th = allocationTotal('jason', '15th');
    const asia1st = allocationTotal('asia', '1st');
    const asia15th = allocationTotal('asia', '15th');
    const selectCycle = (first, second) => metricCycle === '1st' ? first : metricCycle === '15th' ? second : first + second;
    const formatMoney = value => `${value < 0 ? '-' : ''}$${Math.abs(value).toFixed(2)}`;
    const setMetric = (valueId, value, subId, subText, tone = value >= 0 ? 'positive' : 'negative') => {
        const element = document.getElementById(valueId);
        element.textContent = formatMoney(value);
        element.className = `card-value ${tone}`;
        document.getElementById(subId).textContent = subText;
    };
    const cycleBreakdown = (first, second) => metricCycle === 'month'
        ? `1st: ${formatMoney(first)} | 15th: ${formatMoney(second)}`
        : `Month: ${formatMoney(first + second)} | ${metricCycle === '1st' ? '15th' : '1st'}: ${formatMoney(metricCycle === '1st' ? second : first)}`;
    document.getElementById('bills-metrics-title').textContent = `${ownership === 'personal' ? 'Personal' : 'Joint'} Bill Splitter Metrics — ${selectedCycleLabel}`;
    document.querySelectorAll('[data-bills-metrics-cycle]').forEach(button => button.classList.toggle('active', button.dataset.billsMetricsCycle === metricCycle));
    document.getElementById('bills-expenses-title').textContent = `${ownership === 'personal' ? 'Personal' : 'Joint'} Expenses`;
    setMetric('bills-expenses-total', selectCycle(expense1st, expense15th), 'bills-expenses-sub', cycleBreakdown(expense1st, expense15th), 'negative');
    setMetric('bills-jason-allocations', selectCycle(jason1st, jason15th), 'bills-jason-allocations-sub', cycleBreakdown(jason1st, jason15th), 'positive');
    setMetric('bills-asia-allocations', selectCycle(asia1st, asia15th), 'bills-asia-allocations-sub', cycleBreakdown(asia1st, asia15th), 'positive');
    const monthIndex = MONTH_ORDER.indexOf(state.currentMonth);
    const date15th = `${state.currentYear}-${String(monthIndex + 1).padStart(2, '0')}-15`;
    const nextMonth = monthIndex === 11 ? 'Jan' : MONTH_ORDER[monthIndex + 1];
    const nextYear = monthIndex === 11 ? state.currentYear + 1 : state.currentYear;
    const endMonthDate = `${nextYear}-${String(MONTH_ORDER.indexOf(nextMonth) + 1).padStart(2, '0')}-01`;
    const balanceAt = ownership === 'personal'
        ? date => getPersonalRunningBalanceAtDate(date, false)
        : getJointRunningBalanceAtDate;
    const endFirstCycle = balanceAt(date15th);
    const endMonthBalance = balanceAt(endMonthDate);
    const selectedBalance = metricCycle === '1st' ? endFirstCycle : endMonthBalance;
    document.getElementById('bills-balance-title').textContent = `${ownership === 'personal' ? 'Personal' : 'Joint'} Remaining Balance`;
    setMetric('bills-balance-total', selectedBalance, 'bills-balance-sub', `End of 1st: ${formatMoney(endFirstCycle)} | End of month: ${formatMoney(endMonthBalance)}`);
}
// Generic per-column searchable multi-select filter, shared by the Joint/Personal Bills, Personal
// Allocations, and Seasonal Expenses tables. Operates purely on the rendered DOM: each column's
// distinct values are read straight off the current tbody rows (using each cell's bolded primary
// text where present), and matching is done by hiding/showing <tr> elements after render — no
// changes needed to the tables' existing data-building/sorting logic. Filter selections are kept
// in-memory only (not persisted), keyed by "tableKey:columnIndex", each value a Set of the checked
// options (empty Set = no filter applied for that column).
const columnFilterState = {};

function getColumnFilterSet(filterKey) {
    if (!columnFilterState[filterKey]) columnFilterState[filterKey] = new Set();
    return columnFilterState[filterKey];
}

function getColumnCellValue(tr, colIndex) {
    const td = tr.children[colIndex];
    if (!td) return '';
    const strong = td.querySelector('strong');
    return (strong ? strong.textContent : td.textContent).replace(/\s+/g, ' ').trim();
}

function closeAllColumnFilterPopovers() {
    document.querySelectorAll('.col-filter-popover').forEach(p => p.remove());
}

// Hides/shows <tr> elements in `tbody` based on every active filter recorded for `tableKey`. A
// column only filters when at least one of its checkboxes is selected.
function applyColumnFilters(tbody, tableKey) {
    if (!tbody) return;
    const activeCols = Object.keys(columnFilterState)
        .filter(k => k.startsWith(tableKey + ':') && columnFilterState[k] && columnFilterState[k].size > 0)
        .map(k => ({ col: Number(k.split(':')[1]), values: columnFilterState[k] }));
    [...tbody.querySelectorAll(':scope > tr')].forEach(tr => {
        const visible = activeCols.every(f => f.values.has(getColumnCellValue(tr, f.col)));
        tr.style.display = visible ? '' : 'none';
    });
}

// Wires a filter button into a <th> (idempotent — safe to call on every render since <thead> markup
// is static and never rebuilt). `tbody` is passed as a function so it's re-resolved fresh each time
// the popover is opened, in case the element was replaced.
function setupColumnFilterButton(th, tableKey, colIndex, getTbody) {
    if (th.querySelector('.col-filter-btn')) return;
    if (!th.querySelector('.col-th-inner')) {
        const wrapper = document.createElement('span');
        wrapper.className = 'col-th-inner';
        while (th.firstChild) wrapper.appendChild(th.firstChild);
        th.appendChild(wrapper);
    }
    const filterKey = `${tableKey}:${colIndex}`;
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'col-filter-btn';
    btn.title = 'Filter this column';
    btn.textContent = '▾';
    btn.addEventListener('click', (e) => {
        e.stopPropagation();
        const wasOpen = !!th.querySelector('.col-filter-popover');
        closeAllColumnFilterPopovers();
        if (wasOpen) return;

        const tbody = getTbody();
        if (!tbody) return;
        const values = Array.from(new Set(
            [...tbody.querySelectorAll(':scope > tr')].map(tr => getColumnCellValue(tr, colIndex)).filter(Boolean)
        )).sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));

        const popover = document.createElement('div');
        popover.className = 'col-filter-popover';
        popover.addEventListener('click', (ev) => ev.stopPropagation());
        const search = document.createElement('input');
        search.type = 'text';
        search.placeholder = 'Search…';
        search.className = 'col-filter-search';
        const list = document.createElement('div');
        list.className = 'col-filter-list';
        popover.appendChild(search);
        popover.appendChild(list);
        th.appendChild(popover);

        const selected = getColumnFilterSet(filterKey);
        const makeOption = (label, checked, onToggle, extraClass = '') => {
            const row = document.createElement('label');
            row.className = 'col-filter-option' + (extraClass ? ' ' + extraClass : '');
            const cb = document.createElement('input');
            cb.type = 'checkbox';
            cb.checked = checked;
            cb.addEventListener('change', () => onToggle(cb.checked));
            row.appendChild(cb);
            row.appendChild(document.createTextNode(label));
            return row;
        };
        const renderList = (searchText) => {
            list.innerHTML = '';
            const matches = values.filter(v => v.toLowerCase().includes(searchText.toLowerCase()));
            const allChecked = matches.length > 0 && matches.every(v => selected.has(v));
            list.appendChild(makeOption('All', allChecked, (checked) => {
                matches.forEach(v => checked ? selected.add(v) : selected.delete(v));
                applyColumnFilters(getTbody(), tableKey);
                btn.classList.toggle('active', selected.size > 0);
                renderList(search.value);
            }, 'col-filter-all'));
            if (!matches.length) {
                const empty = document.createElement('div');
                empty.className = 'col-filter-empty';
                empty.textContent = 'No matches';
                list.appendChild(empty);
            }
            matches.forEach(v => {
                list.appendChild(makeOption(v, selected.has(v), (checked) => {
                    checked ? selected.add(v) : selected.delete(v);
                    applyColumnFilters(getTbody(), tableKey);
                    btn.classList.toggle('active', selected.size > 0);
                    renderList(search.value);
                }));
            });
        };
        renderList('');
        search.addEventListener('input', () => renderList(search.value));
        search.focus();
    });
    if (getColumnFilterSet(filterKey).size > 0) btn.classList.add('active');
    th.appendChild(btn);
}

// Attaches filter buttons to every <th> in `theadSelector` except those listed in `skipCols`.
function setupTableColumnFilters(theadSelector, tableKey, getTbody, skipCols = []) {
    const headerRow = document.querySelector(`${theadSelector} tr`);
    if (!headerRow) return;
    [...headerRow.children].forEach((th, colIndex) => {
        if (skipCols.includes(colIndex)) return;
        setupColumnFilterButton(th, tableKey, colIndex, getTbody);
    });
}

document.addEventListener('click', (e) => {
    if (!e.target.closest('.col-filter-popover') && !e.target.closest('.col-filter-btn')) {
        closeAllColumnFilterPopovers();
    }
});

// Describes a non-monthly subscription bill by the weekday it recurs on (e.g. "Weekly on
// Wednesdays", "Every 2 weeks on Fridays") instead of the raw anchor date, since the weekday is what
// actually repeats — the date itself was just the first occurrence. Quarterly/annual charges fall
// back to the anchor date since "day of week" isn't a meaningful way to describe something that
// happens once every several months.
const WEEKDAY_NAMES = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
function getSubscriptionDayLabel(bill, frequencyLabels) {
    const label = frequencyLabels[bill.chargeFrequency] || bill.chargeFrequency;
    if (bill.chargeFrequency === 'quarterly' || bill.chargeFrequency === 'annual') {
        return `${label} from ${bill.frequencyStartDate}`;
    }
    if (bill.frequencyStartDate) {
        const weekdayName = new Date(bill.frequencyStartDate + 'T00:00:00').toLocaleDateString('en-US', { weekday: 'long' });
        return `${label} on ${weekdayName}s`;
    }
    // Legacy weekly bills store the recurring weekday directly (weeklyDay: 0-6) instead of an anchor date.
    if (Number.isInteger(bill.weeklyDay)) {
        return `${label} on ${WEEKDAY_NAMES[bill.weeklyDay]}s`;
    }
    return label;
}
function renderBillsTab() {
    const key = `${state.currentYear}-${state.currentMonth}`;
    ensureYearMonthInitialized(state.currentYear, state.currentMonth);
    autopopulateBillsForMonth(state.currentYear, state.currentMonth);
    applyAllocationTemplatesForMonth(state.currentYear, state.currentMonth);
    applySeasonalExpensesForMonth(state.currentYear, state.currentMonth);
    applySeasonalChargeForMonth(state.currentYear, state.currentMonth);
    const mBills = state.monthlyBills[key];
    if (!mBills) return;

    const currentCycle = state.billMetricsCycle || 'month';

    const allBills = ['cycle1st', 'cycle15th'].flatMap(cycleKey => (mBills[cycleKey].bills || []).map(bill => normalizeBillSplitterItem(bill, cycleKey)));
    renderBillSplitterMetrics(mBills, allBills);
    const calcBillsSplit = (cycleData, cycleKey) => {
        let jointBudget = 0;
        allBills.forEach(bill => {
            const assignedCycle = bill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st';
            const allocatedAmount = bill.cycleAllocation === 'both' ? bill.budgetAmount / 2 : (assignedCycle === cycleKey ? bill.budgetAmount : 0);
            if (bill.ownership !== 'personal') jointBudget += allocatedAmount;
        });
        // Preserve sign: negative "offset" allocations are meant to net against other allocations,
        // not add to them. 'both'-cycle allocations split half/half via getAllocationCycleTotal.
        const jasonAllocations = getAllocationCycleTotal(mBills, cycleKey, 'jason');
        const asiaAllocations = getAllocationCycleTotal(mBills, cycleKey, 'asia');
        const jointShare = Math.round(jointBudget * 50 + 1e-8) / 100;
        return {
            jasonTotal: Math.round((jasonAllocations + jointShare) * 100 + 1e-8) / 100,
            asiaTotal: Math.round((asiaAllocations + jointShare) * 100 + 1e-8) / 100
        };
    };

    const split1st = calcBillsSplit(mBills.cycle1st, 'cycle1st');
    const split15th = calcBillsSplit(mBills.cycle15th, 'cycle15th');
    const monthPrefix = `${state.currentYear}-${String(MONTH_ORDER.indexOf(state.currentMonth) + 1).padStart(2, '0')}-`;
    const monthlyManualTransfers = (state.manualTransfers || []).filter(transfer => transfer.date.startsWith(monthPrefix)).sort((a, b) => a.date.localeCompare(b.date));
    const manualByCycle = { jason1st: 0, jason15th: 0, asia1st: 0, asia15th: 0 };
    monthlyManualTransfers.forEach(transfer => {
        const cycle = Number(transfer.date.slice(8, 10)) < 15 ? '1st' : '15th';
        const person = transfer.person === 'asia' ? 'asia' : 'jason';
        manualByCycle[`${person}${cycle}`] += Number(transfer.amount) || 0;
    });
    const jason1st = split1st.jasonTotal + manualByCycle.jason1st;
    const jason15th = split15th.jasonTotal + manualByCycle.jason15th;
    const asia1st = split1st.asiaTotal + manualByCycle.asia1st;
    const asia15th = split15th.asiaTotal + manualByCycle.asia15th;
    document.getElementById('jason-transfer-1st').textContent = `$${jason1st.toFixed(2)}`;
    document.getElementById('jason-transfer-15th').textContent = `$${jason15th.toFixed(2)}`;
    document.getElementById('asia-transfer-1st').textContent = `$${asia1st.toFixed(2)}`;
    document.getElementById('asia-transfer-15th').textContent = `$${asia15th.toFixed(2)}`;
    document.getElementById('jason-transfer').textContent = `Monthly Total: $${(jason1st + jason15th).toFixed(2)}`;
    document.getElementById('asia-transfer').textContent = `Monthly Total: $${(asia1st + asia15th).toFixed(2)}`;

    const manualTransfersBody = document.getElementById('manual-transfers-body');
    manualTransfersBody.innerHTML = '';
    let displayManual = monthlyManualTransfers;
    if (currentCycle !== 'month') {
        displayManual = displayManual.filter(t => {
            const cycle = Number(t.date.slice(8, 10)) < 15 ? '1st' : '15th';
            return cycle === currentCycle;
        });
    }
    displayManual.forEach(transfer => {
        const cycle = Number(transfer.date.slice(8, 10)) < 15 ? '1st' : '15th';
        const row = document.createElement('tr');
        row.innerHTML = `<td>${transfer.date}</td><td>${transfer.person === 'asia' ? 'Asia' : 'Jason'}</td><td>${escapeHTML(transfer.description)}</td><td>${cycle}</td><td class="positive font-heading">+$${Number(transfer.amount).toFixed(2)}</td><td><button type="button" class="action-btn small-btn danger-btn delete-manual-transfer-btn">Delete</button></td>`;
        row.querySelector('.delete-manual-transfer-btn').addEventListener('click', () => {
            if (!confirm(`Delete the planned transfer on ${transfer.date}?`)) return;
            state.manualTransfers = (state.manualTransfers || []).filter(item => item.id !== transfer.id);
            state.jointRegister = (state.jointRegister || []).filter(item => item.linkedManualTransferId !== transfer.id);
            Object.keys(state.personalCalendar || {}).forEach(key => {
                state.personalCalendar[key] = (state.personalCalendar[key] || []).filter(item => item.linkedManualTransferId !== transfer.id);
            });
            saveDatabase();
            renderApp();
        });
        manualTransfersBody.appendChild(row);
    });
    if (!displayManual.length) manualTransfersBody.innerHTML = '<tr><td colspan="6" class="muted-text" style="text-align:center;">No manual transfers planned for this period.</td></tr>';

    const jointBody = document.getElementById('joint-bills-body');
    jointBody.innerHTML = '';
    const ownershipFilter = state.billTrackerOwnership || 'joint';
    document.getElementById('bill-tracker-title').textContent = ownershipFilter === 'personal' ? 'Personal Expenses' : 'Joint Expenses';
    document.getElementById('btn-add-joint-bill').textContent = ownershipFilter === 'personal' ? '+ Add Personal Expense' : '+ Add Joint Expense';
    document.querySelectorAll('#bill-ownership-toggle [data-bill-ownership]').forEach(button => {
        button.classList.toggle('active', button.dataset.billOwnership === ownershipFilter);
    });
    const categoryFilter = document.getElementById('bill-category-filter').value;
    const billSort = state.billTrackerSorts?.[ownershipFilter] || { key: ownershipFilter === 'personal' ? 'dueDay' : 'account', direction: 'asc' };
    document.getElementById('bill-sort-select').classList.add('hidden');
    // Text is set on the wrapper span (not the <th> itself) once column-filter buttons have been
    // wired in, since setting .textContent directly on the <th> would wipe out the filter button.
    const dateHeaderEl = document.getElementById('bill-date-header');
    const dateHeaderLabel = ownershipFilter === 'personal' ? 'Charge Day' : 'Day';
    const dateHeaderInner = dateHeaderEl.querySelector('.col-th-inner');
    if (dateHeaderInner) dateHeaderInner.textContent = dateHeaderLabel; else dateHeaderEl.textContent = dateHeaderLabel;
    let displayBills = ['cycle1st', 'cycle15th'].flatMap(cycleKey =>
        (mBills[cycleKey].bills || []).map((rawBill, idx) => ({ bill: normalizeBillSplitterItem(rawBill, cycleKey), cycleKey, idx }))
    );
    displayBills.forEach(entry => { mBills[entry.cycleKey].bills[entry.idx] = entry.bill; });
    displayBills = displayBills.filter(entry => (entry.bill.ownership || 'joint') === ownershipFilter);
    if (currentCycle !== 'month') {
        displayBills = displayBills.filter(entry => {
            const alloc = entry.bill.cycleAllocation;
            return alloc === currentCycle || alloc === 'both';
        });
    }
    if (categoryFilter !== 'all') displayBills = displayBills.filter(entry => entry.bill.category === categoryFilter);
    displayBills.sort((a, b) => {
        const value = entry => {
            const bill = entry.bill;
            if (billSort.key === 'dueDay') {
                // Monthly charges sort numerically by day-of-month (0-31). Subscriptions (weekly,
                // biweekly, etc.) don't have a meaningful day-of-month, so they're grouped together
                // below all numeric days, ordered by frequency type then by weekday.
                if (bill.chargeFrequency === 'monthly') return Number(bill.dueDay) || 0;
                const freqOrder = { weekly: 0, biweekly: 1, fourweekly: 2, quarterly: 3, annual: 4 }[bill.chargeFrequency] ?? 5;
                const weekday = bill.frequencyStartDate
                    ? new Date(bill.frequencyStartDate + 'T00:00:00').getDay()
                    : (Number.isInteger(bill.weeklyDay) ? bill.weeklyDay : 0);
                return 1000 + freqOrder * 10 + weekday;
            }
            if (billSort.key === 'budgetAmount' || billSort.key === 'paymentAmount') return Number(bill[billSort.key]) || 0;
            if (billSort.key === 'isRecurring') return bill.isRecurring ? 1 : 0;
            return String(bill[billSort.key] || '').toLowerCase();
        };
        const first = value(a); const second = value(b);
        const comparison = typeof first === 'number' ? first - second : first.localeCompare(second);
        return billSort.direction === 'desc' ? -comparison : comparison;
    });

    displayBills.forEach(({ bill, cycleKey, idx }) => {
        const sourceName = bill.paymentSource === 'jointChecking' ? 'Joint Checking' : bill.paymentSource === 'personalChecking' ? 'Personal Checking' : (state.loans.find(card => card.id === bill.paymentSource)?.name || 'Credit Card');
        const cycleLabel = bill.cycleAllocation === 'both' ? '1st & 15th' : (bill.cycleAllocation === '15th' ? '15th' : '1st');
        const frequencyLabels = { monthly: 'Monthly', weekly: 'Weekly', biweekly: 'Every 2 weeks', fourweekly: 'Every 4 weeks', quarterly: 'Every 3 months', annual: 'Annual' };
        const budgetDetail = `${frequencyLabels[bill.chargeFrequency] || 'Monthly'} charge: $${bill.frequencyAmount.toFixed(2)} | ${bill.budgetFrequency === 'monthly' ? 'spread monthly' : bill.weeklyOccurrences + ' charge(s) this month'}`;
        const categoryLabels = { bill: 'Bill', expense: 'Expense', utility: 'Utility', savings: 'Savings / Investments' };
        const categoryLabel = categoryLabels[bill.category] || (bill.category.charAt(0).toUpperCase() + bill.category.slice(1));
        const isAutoCardOrLoan = !!bill.linkedCardPaymentId && bill.cardPaymentKind === 'auto';
        const linkedTarget = bill.linkedCardPaymentId && bill.payoffTargetId ? state.loans.find(l => l.id === bill.payoffTargetId) : null;
        const mortgageTarget = bill.isMortgage && bill.mortgageLoanId ? state.loans.find(l => l.id === bill.mortgageLoanId) : null;
        const recurringRange = mortgageTarget
            ? `Yes<br><span class="muted-text">${mortgageTarget.paymentEndDate ? 'Through ' + mortgageTarget.paymentEndDate : 'Ongoing'}</span>`
            : (bill.isRecurring
                ? `Yes<br><span class="muted-text">${bill.recurringStartMonth ? 'Starts ' + bill.recurringStartMonth : 'Current'}${bill.recurringEndMonth ? ' through ' + bill.recurringEndMonth : ''}</span>`
                : (isAutoCardOrLoan
                    ? `Yes<br><span class="muted-text">${linkedTarget && linkedTarget.paymentEndDate ? 'Through ' + linkedTarget.paymentEndDate : 'Ongoing'}</span>`
                    : 'No'));
        const row = document.createElement('tr');
        row.innerHTML = `
            <td><strong>${escapeHTML(bill.account)}</strong></td>
            <td><strong>${categoryLabel}</strong>${bill.billTrackerCategory ? `<br><span class="muted-text">${escapeHTML(bill.billTrackerCategory)}</span>` : ''}<br>${bill.entryType === 'actual' ? 'Actual Charge' : 'Transfer Only'}<br><span class="muted-text">${bill.ownership === 'joint' ? 'Joint' : 'Personal'}</span></td>
            <td>${getBillIndicatorBadge(bill)}</td>
            <td>${cycleLabel}</td>
            <td>${bill.chargeFrequency === 'monthly' ? 'Day ' + bill.dueDay : getSubscriptionDayLabel(bill, frequencyLabels)}</td>
            <td class="font-heading">$${bill.budgetAmount.toFixed(2)}<br><span class="muted-text">${bill.cycleAllocation === 'both' ? '1st: $' + (bill.budgetAmount / 2).toFixed(2) + ' | 15th: $' + (bill.budgetAmount / 2).toFixed(2) : budgetDetail}</span></td>
            <td class="${bill.entryType === 'actual' ? 'negative' : ''} font-heading">${bill.entryType === 'actual' ? '$' + bill.paymentAmount.toFixed(2) : '—'}</td>
            <td>${bill.entryType === 'actual' ? sourceName : 'Not posted'}</td>
            <td>${recurringRange}</td>
            <td class="table-actions-cell"><button class="action-btn small-btn edit-bill-btn">Edit</button><button class="action-btn small-btn danger-btn delete-bill-btn">Delete</button></td>`;
        row.querySelector('.edit-bill-btn').addEventListener('click', () => openBillSplitterEditor(bill, cycleKey));
        row.querySelector('.delete-bill-btn').addEventListener('click', () => {
            if (bill.linkedCardPaymentId) {
                const linkedAccount = bill.payoffTargetId ? state.loans.find(l => l.id === bill.payoffTargetId) : null;
                const isLoanLinked = linkedAccount && linkedAccount.type === 'loan';
                const accountLabel = isLoanLinked ? 'loan' : 'credit card';
                const sectionLabel = isLoanLinked ? 'Installment Loans' : 'Credit Cards';
                if (confirm(`This entry is synchronized from a ${accountLabel} payment and cannot be deleted here. Manage the payment under ${sectionLabel} instead.\n\nGo there now?`)) {
                    goToCardPaymentInCreditCards(bill.payoffTargetId, bill.linkedPaymentDate);
                }
                return;
            }
            if (bill.billTrackerSettingId) {
                const dialog = document.getElementById('delete-billtracker-warning-dialog');
                if (dialog) {
                    const goBtn = document.getElementById('link-to-delete-master-setting');
                    if (goBtn) {
                        goBtn.onclick = () => {
                            dialog.close();
                            switchToTab('billtracker');
                            renderBillTrackerTab();
                            openEditBillSettingModal(bill.billTrackerSettingId);
                        };
                    }
                    dialog.showModal();
                }
                return;
            }
            if (!confirm(`Delete ${bill.account} from ${MONTH_NAMES[state.currentMonth]} ${state.currentYear}?`)) return;
            const deleteFuture = confirm(`Also delete ${bill.account} from every future month?\n\nOK = this month and all future months\nCancel = this month only`);
            const removedCount = deleteBillSplitterItem(bill, state.currentYear, state.currentMonth, deleteFuture);
            saveDatabase();
            renderApp();
            logSystem(`Deleted Bill Splitter item: ${bill.account}${deleteFuture ? ` (${removedCount} current/future entries)` : ' (this month only)'}`);
        });
        jointBody.appendChild(row);
    });
    if (!displayBills.length) jointBody.innerHTML = `<tr><td colspan="8" class="muted-text" style="text-align:center;">${categoryFilter === 'all' ? 'No Bill Splitter items logged for this period.' : 'No items match this category filter.'}</td></tr>`;
    setupTableColumnFilters('#joint-expenses-content thead', 'jointBills', () => document.getElementById('joint-bills-body'), [9]);
    applyColumnFilters(jointBody, 'jointBills');
    const personalBody = document.getElementById('personal-allocations-body');
    personalBody.innerHTML = '';
    const allocationEntries = ['1st', '15th'].flatMap(cycle => {
        const cycleKey = cycle === '1st' ? 'cycle1st' : 'cycle15th';
        return (mBills[cycleKey].contributions || []).map((alloc, idx) => ({ alloc, idx, cycle, cycleKey }));
    });
    let displayAllocations = allocationEntries;
    if (currentCycle !== 'month') {
        // 'both'-cycle allocations physically live in the cycle1st array (alloc.cycle === 'both'),
        // not the array-iteration cycle — check the actual stored value, same pattern as bills.
        displayAllocations = displayAllocations.filter(entry => entry.alloc.cycle === currentCycle || entry.alloc.cycle === 'both');
    }
    const allocationSort = state.billTrackerSorts?.allocations || { key: 'name', direction: 'asc' };
    displayAllocations.sort((a, b) => {
        const value = entry => {
            if (allocationSort.key === 'cycle') return entry.alloc.cycle === '1st' ? 1 : entry.alloc.cycle === 'both' ? 8 : 15;
            if (allocationSort.key === 'jason' || allocationSort.key === 'asia') return Number(entry.alloc[allocationSort.key]) || 0;
            return String(entry.alloc.name || '').toLowerCase();
        };
        const first = value(a); const second = value(b);
        const comparison = typeof first === 'number' ? first - second : first.localeCompare(second);
        return allocationSort.direction === 'desc' ? -comparison : comparison;
    });
    displayAllocations.forEach(({ alloc, idx, cycle, cycleKey }) => {
            const row = document.createElement('tr');
            if (!alloc.id) alloc.id = 'alloc-' + Math.random().toString(36).substr(2, 9);
            const isRecurring = !!state.allocationTemplates[alloc.seriesId];
            const formatAllocationAmount = (value, isPersonRecurring) => {
                if (value === null || value === undefined || value === '') return '<span class="muted-text">&mdash;</span>';
                const amount = Number(value) || 0;
                const sign = amount > 0 ? '+' : amount < 0 ? '-' : '';
                const icon = (isRecurring && isPersonRecurring) ? ' <span class="recurring-icon" title="Recurring allocation" style="font-size: 0.85rem; margin-left: 4px; cursor: help;">🔁</span>' : '';
                return `<span class="${amount < 0 ? 'negative' : 'positive'}">${sign}$${Math.abs(amount).toFixed(2)}</span>${icon}`;
            };
            const jasonHtml = formatAllocationAmount(alloc.jason, alloc.jason !== null && alloc.jason !== undefined && Number(alloc.jason) !== 0);
            const asiaHtml = formatAllocationAmount(alloc.asia, alloc.asia !== null && alloc.asia !== undefined && Number(alloc.asia) !== 0);
            const cycleDisplay = alloc.cycle === 'both' ? '1st & 15th' : cycle;
            row.innerHTML = `<td><strong>${escapeHTML(alloc.name)}</strong><br><span class="muted-text">${(alloc.frequency || 'monthly').charAt(0).toUpperCase() + (alloc.frequency || 'monthly').slice(1)}${alloc.frequency === 'weekly' ? ' Â· ' + (alloc.occurrenceCount || 0) + ' occurrences this month' : ''}</span></td><td><span class="card-icon info" style="font-size:.75rem;padding:2px 6px;">Due on ${cycleDisplay}</span></td><td class="font-heading">${jasonHtml}</td><td class="font-heading">${asiaHtml}</td><td class="table-actions-cell"><button class="action-btn small-btn outline-btn edit-alloc-btn">Edit</button> <button class="action-btn small-btn danger-btn delete-alloc-btn">Delete</button></td>`;
            row.querySelector('.edit-alloc-btn').addEventListener('click', () => openAllocationEditor(alloc, cycleKey));
            row.querySelector('.delete-alloc-btn').addEventListener('click', () => {
                if (!confirm(`Delete ${alloc.name} from ${state.currentMonth} ${state.currentYear}?`)) return;
                const deleteFuture = confirm(`Also delete this allocation from all future months?\n\nOK = current and future\nCancel = current month only`);
                deleteAllocationOccurrence(alloc, state.currentYear, state.currentMonth, deleteFuture);
                saveDatabase();
                renderApp();
                logSystem(`Deleted personal allocation: ${alloc.name}${deleteFuture ? ' (current and future)' : ' (current month only)'}`);
            });
            personalBody.appendChild(row);
    });
    if (!displayAllocations.length) personalBody.innerHTML = '<tr><td colspan="5" class="muted-text" style="text-align:center;">No personal allocations logged for this period.</td></tr>';
    setupTableColumnFilters('#personal-allocations-content thead', 'personalAllocations', () => document.getElementById('personal-allocations-body'), [4]);
    applyColumnFilters(personalBody, 'personalAllocations');
    const seasonalBody = document.getElementById('seasonal-expenses-body');
    seasonalBody.innerHTML = '';
    const seasonalSort = state.billTrackerSorts.seasonal || { key: 'month', direction: 'asc' };
    const sortedSeasonalExpenses = [...(state.seasonalExpenses || [])].sort((a, b) => {
        const value = expense => {
            if (seasonalSort.key === 'amount') return Number(expense.amount) || 0;
            if (seasonalSort.key === 'cycles') return Number(expense.cycles) || 0;
            if (seasonalSort.key === 'month') return expense.startDate || '';
            return String(expense[seasonalSort.key] || '').toLowerCase();
        };
        const first = value(a); const second = value(b);
        const comparison = typeof first === 'number' ? first - second : first.localeCompare(second);
        return seasonalSort.direction === 'desc' ? -comparison : comparison;
    });
    sortedSeasonalExpenses.forEach(expense => {
        const row = document.createElement('tr');
        const installment = expense.amount / expense.cycles;
        const seasonalDateRange = expense.startDate + (expense.endDate ? ` &ndash; ${expense.endDate}` : '');
        const frequencyLabel = expense.isRecurring ? `Repeats ${expense.frequency || 'yearly'}` : 'One-time';
        const chargeLabel = expense.hasCharge ? `$${Number(expense.chargeAmount || 0).toFixed(2)} on ${expense.chargeDate} (${expense.chargeSource === 'joint' ? 'Joint' : 'Personal'})` : '&mdash;';
        row.innerHTML = `<td><strong>${escapeHTML(expense.name)}</strong></td><td>${seasonalDateRange}</td><td>$${expense.amount.toFixed(2)}</td><td>${expense.cycles} cycles × $${installment.toFixed(2)}</td><td>${frequencyLabel}</td><td>${chargeLabel}</td><td><button class="action-btn small-btn outline-btn edit-seasonal-btn">Edit</button> <button class="action-btn small-btn danger-btn delete-seasonal-btn">Delete</button></td>`;
        row.querySelector('.edit-seasonal-btn').addEventListener('click', () => openSeasonalEditor(expense));
        row.querySelector('.delete-seasonal-btn').addEventListener('click', () => {
            if (!confirm(`Delete ${expense.name} and its generated funding entries?`)) return;
            removeSeasonalInstallments(expense.id); state.seasonalExpenses = state.seasonalExpenses.filter(item => item.id !== expense.id); saveDatabase(); renderApp();
        });
        seasonalBody.appendChild(row);
    });
    setupTableColumnFilters('#seasonal-expenses-content thead', 'seasonal', () => document.getElementById('seasonal-expenses-body'), [6]);
    applyColumnFilters(seasonalBody, 'seasonal');
    // The card itself (header + "Add Seasonal Expense" button) always stays visible so there's a way
    // to add the first one — only the "no items" placeholder text is skipped when empty, leaving the
    // table body simply blank instead.
}
// 4. RENDER DELIVERY EARNINGS TAB (Platform totals & weekly grid)
function renderDeliveryTab() {
    const month = state.currentMonth;
    
    // Filter gig earnings for current month & year
    const gigs = state.deliveryEarnings.filter(g => {
        const dateObj = new Date(g.date + 'T00:00:00');
        const mShort = MONTH_ORDER[dateObj.getMonth()];
        return dateObj.getFullYear() === state.currentYear && mShort === month;
    });
    
    // Platform Breakdown
    const totals = { cash: 0, sideGigs: 0, grubHub: 0, uberEats: 0, grandTotal: 0 };
    gigs.forEach(g => {
        totals.cash += g.cash || 0;
        totals.sideGigs += g.sideGigs || 0;
        totals.grubHub += g.grubHub || 0;
        totals.uberEats += g.uberEats || 0;
        totals.grandTotal += g.total || 0;
    });
    
    // Render Bars
    const barsContainer = document.getElementById('platform-bars');
    barsContainer.innerHTML = '';
    
    const platforms = [
        { key: 'cash', label: 'Cash', value: totals.cash },
        { key: 'sideGigs', label: 'Door Dash', value: totals.sideGigs },
        { key: 'grubHub', label: 'Grub Hub', value: totals.grubHub },
        { key: 'uberEats', label: 'Uber Eats', value: totals.uberEats }
    ];
    
    const maxVal = Math.max(...platforms.map(p => p.value), 1);
    
    platforms.forEach(p => {
        const widthPct = (p.value / maxVal) * 100;
        const row = document.createElement('div');
        row.className = 'platform-bar-row';
        row.innerHTML = `
            <span class="platform-label">${p.label}</span>
            <div class="platform-track">
                <div class="platform-fill" style="width: ${widthPct}%"></div>
            </div>
            <span class="platform-value">$${p.value.toFixed(0)}</span>
        `;
        barsContainer.appendChild(row);
    });

    // Group gigs into Mon-Sun weeks dynamically
    const weeks = getDeliveryWeeksForMonth(month);
    
    // Adjust week index bounds
    if (state.deliveryWeekIndex >= weeks.length) {
        state.deliveryWeekIndex = Math.max(0, weeks.length - 1);
    }
    if (state.deliveryWeekIndex < 0) {
        state.deliveryWeekIndex = 0;
    }
    
    if (weeks.length === 0) {
        document.getElementById('weekly-totals-list').innerHTML = `<p class="muted-text">No data for this period.</p>`;
        document.getElementById('delivery-log-body').innerHTML = `<tr><td colspan="10" class="muted-text" style="text-align:center;">No logs found.</td></tr>`;
        document.getElementById('delivery-week-label').textContent = 'No week available';
        return;
    }
    
    const activeWeek = weeks[state.deliveryWeekIndex];
    
    // Render Weekly Totals list in sidebar
    const weeklyList = document.getElementById('weekly-totals-list');
    weeklyList.innerHTML = '';
    
    weeks.forEach((w, wIdx) => {
        const wSum = w.reduce((sum, g) => sum + g.total, 0);
        const wBudget = w.reduce((sum, g) => sum + (Number(state.deliveryBudgets?.[g.date]) || 0), 0);
        const startStr = new Date(w[0].date+'T00:00:00').toLocaleDateString('en-US', {month:'short', day:'numeric'});
        const endStr = new Date(w[w.length-1].date+'T00:00:00').toLocaleDateString('en-US', {month:'short', day:'numeric'});
        const item = document.createElement('div');
        item.className = `weekly-total-item ${wIdx === state.deliveryWeekIndex ? 'selected-day' : ''}`;
        item.style.cursor = 'pointer';
        item.innerHTML = `
            <span class="weekly-total-label">Week ${wIdx+1} (${startStr} - ${endStr})</span>
            <span class="weekly-total-val">$${wSum.toFixed(2)} / $${wBudget.toFixed(2)} goal</span>
        `;
        item.addEventListener('click', () => {
            state.deliveryWeekIndex = wIdx;
            renderDeliveryTab();
        });
        weeklyList.appendChild(item);
    });
    
    // Render grid label
    const startStr = new Date(activeWeek[0].date+'T00:00:00').toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
    const endStr = new Date(activeWeek[activeWeek.length-1].date+'T00:00:00').toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
    document.getElementById('delivery-week-label').textContent = `Week of ${startStr} - ${endStr}`;
    
    // Render Grid body
    const gridBody = document.getElementById('delivery-log-body');
    gridBody.innerHTML = '';
    
    activeWeek.forEach(gRecord => {
        const row = document.createElement('tr');
        row.className = gRecord.offDayReason ? 'off-day-row' : '';
        const dailyBudget = Number(state.deliveryBudgets?.[gRecord.date]) || 0;
        const difference = gRecord.total - dailyBudget;
        let diffClass = '';
        let diffText = '—';
        if (dailyBudget > 0) {
            if (difference > 0) {
                diffClass = 'positive';
                diffText = `+$${difference.toFixed(2)}`;
            } else if (difference < 0) {
                diffClass = 'negative';
                diffText = `-$${Math.abs(difference).toFixed(2)}`;
            } else {
                diffClass = '';
                diffText = '$0.00';
            }
        }
        
        let colsHtml = '';
        if (gRecord.offDayReason) {
            colsHtml = `
                <td colspan="4" class="off-day-overlay-cell">🚫 Off-Day: ${escapeHTML(gRecord.offDayReason)}</td>
                <td class="font-heading" style="font-weight:600; text-align:right;">$0.00</td>
            `;
        } else {
            const formatVal = (k) => {
                const val = gRecord[k];
                return val ? `$${val.toFixed(2)}` : '$0.00';
            };
            const mobileReadonly = isMobileViewport() ? 'readonly' : '';
            colsHtml = `
                <td>
                    <div class="gig-cell-content">
                        <textarea class="gig-input" rows="1" data-date="${gRecord.date}" data-key="cash" data-label="Cash" placeholder="$0.00" ${mobileReadonly} ${gRecord.noEarnCash ? 'disabled style="opacity:0.5;"' : ''}>${formatVal('cash')}</textarea>
                        <input type="checkbox" class="gig-no-earn" tabindex="-1" data-date="${gRecord.date}" data-key="cash" ${gRecord.noEarnCash ? 'checked' : ''} title="No earnings">
                    </div>
                </td>
                <td>
                    <div class="gig-cell-content">
                        <textarea class="gig-input" rows="1" data-date="${gRecord.date}" data-key="sideGigs" data-label="Door Dash" placeholder="$0.00" ${mobileReadonly} ${gRecord.noEarnSideGigs ? 'disabled style="opacity:0.5;"' : ''}>${formatVal('sideGigs')}</textarea>
                        <input type="checkbox" class="gig-no-earn" tabindex="-1" data-date="${gRecord.date}" data-key="sideGigs" ${gRecord.noEarnSideGigs ? 'checked' : ''} title="No earnings">
                    </div>
                </td>
                <td>
                    <div class="gig-cell-content">
                        <textarea class="gig-input" rows="1" data-date="${gRecord.date}" data-key="grubHub" data-label="Grub Hub" placeholder="$0.00" ${mobileReadonly} ${gRecord.noEarnGrubHub ? 'disabled style="opacity:0.5;"' : ''}>${formatVal('grubHub')}</textarea>
                        <input type="checkbox" class="gig-no-earn" tabindex="-1" data-date="${gRecord.date}" data-key="grubHub" ${gRecord.noEarnGrubHub ? 'checked' : ''} title="No earnings">
                    </div>
                </td>
                <td>
                    <div class="gig-cell-content">
                        <textarea class="gig-input" rows="1" data-date="${gRecord.date}" data-key="uberEats" data-label="Uber Eats" placeholder="$0.00" ${mobileReadonly} ${gRecord.noEarnUberEats ? 'disabled style="opacity:0.5;"' : ''}>${formatVal('uberEats')}</textarea>
                        <input type="checkbox" class="gig-no-earn" tabindex="-1" data-date="${gRecord.date}" data-key="uberEats" ${gRecord.noEarnUberEats ? 'checked' : ''} title="No earnings">
                    </div>
                </td>
                <td class="font-heading" style="font-weight:600; text-align:right;">$${gRecord.total.toFixed(2)}</td>
            `;
        }
        
        const storedBudget = Number(state.deliveryBudgets?.[gRecord.date]) || 0;
        row.innerHTML = `
            <td>
                <div style="display:flex; align-items:center;">
                    <input type="checkbox" class="day-off-toggle" tabindex="-1" data-date="${gRecord.date}" ${gRecord.offDayReason ? 'checked' : ''} title="Mark as Off-Day (Strike through entire day)">
                    <strong>${gRecord.date}</strong>
                </div>
            </td>
            <td><span class="card-icon info" style="font-size:0.75rem; padding: 2px 6px;">${gRecord.day}</span></td>
            ${colsHtml}
            <td>
                <input type="text" class="gig-budget-input" tabindex="-1" data-date="${gRecord.date}" value="${storedBudget > 0 ? storedBudget : ''}" placeholder="—">
            </td>
            <td class="${diffClass} font-heading" style="text-align:right;">${diffText}</td>
            <td>
                <input type="text" class="gig-off-day-input" tabindex="-1" data-date="${gRecord.date}" value="${escapeHTML(gRecord.offDayReason || '')}" placeholder="e.g. Vacation">
            </td>
        `;
        
        // 1. Gig input change/focus/blur/keydown listeners
        row.querySelectorAll('.gig-input').forEach(input => {
            const key = input.dataset.key;

            input.addEventListener('click', (e) => {
                if (input.hasAttribute('readonly') && !input.disabled) {
                    openGigEntryDialog(gRecord.date, key, input.dataset.label);
                }
            });

            input.addEventListener('focus', (e) => {
                const rec = state.deliveryEarnings.find(item => item.date === gRecord.date);
                if (rec) {
                    e.target.value = rec[key + 'Formula'] || (rec[key] ? String(rec[key]) : '');
                    e.target.select();
                }
            });
            
            input.addEventListener('blur', (e) => {
                const rec = state.deliveryEarnings.find(item => item.date === gRecord.date);
                if (rec) {
                    const val = rec[key];
                    e.target.value = val ? `$${val.toFixed(2)}` : '$0.00';
                }
            });
            
            input.addEventListener('keydown', (e) => {
                if (e.key === 'Enter') {
                    e.preventDefault();
                    e.target.blur();
                } else if (e.key === 'Tab') {
                    const keysOrder = ['cash', 'sideGigs', 'grubHub', 'uberEats'];
                    const currentIdx = keysOrder.indexOf(key);
                    let nextDate = null;
                    let nextKey = null;
                    
                    if (e.shiftKey) {
                        // Shift+Tab: Go backward
                        if (currentIdx > 0) {
                            nextDate = gRecord.date;
                            nextKey = keysOrder[currentIdx - 1];
                        } else {
                            const dayIdx = activeWeek.findIndex(d => d.date === gRecord.date);
                            if (dayIdx > 0) {
                                nextDate = activeWeek[dayIdx - 1].date;
                                nextKey = keysOrder[3];
                            }
                        }
                    } else {
                        // Tab: Go forward
                        if (currentIdx < 3) {
                            nextDate = gRecord.date;
                            nextKey = keysOrder[currentIdx + 1];
                        } else {
                            const dayIdx = activeWeek.findIndex(d => d.date === gRecord.date);
                            if (dayIdx >= 0 && dayIdx < activeWeek.length - 1) {
                                nextDate = activeWeek[dayIdx + 1].date;
                                nextKey = keysOrder[0];
                            }
                        }
                    }
                    
                    if (nextDate && nextKey) {
                        e.preventDefault();
                        
                        const rec = state.deliveryEarnings.find(item => item.date === gRecord.date);
                        const currentSavedVal = rec ? (rec[key + 'Formula'] || (rec[key] ? String(rec[key]) : '')) : '';
                        const rawVal = e.target.value.trim();
                        const isChanged = currentSavedVal !== rawVal;
                        
                        if (isChanged) {
                            state.nextFocusDate = nextDate;
                            state.nextFocusKey = nextKey;
                            e.target.blur();
                        } else {
                            const targetInput = document.querySelector(`textarea.gig-input[data-date="${nextDate}"][data-key="${nextKey}"]`);
                            if (targetInput) {
                                targetInput.focus();
                                targetInput.select();
                            }
                        }
                    }
                }
            });
            
            input.addEventListener('change', (e) => {
                const date = e.target.dataset.date;
                const key = e.target.dataset.key;
                const rawVal = e.target.value.trim();
                const parsedVal = parseFormula(rawVal);
                
                const rec = state.deliveryEarnings.find(item => item.date === date);
                if (rec) {
                    rec[key + 'Formula'] = rawVal;
                    rec[key] = parsedVal;
                    rec.total = (rec.cash || 0) + (rec.sideGigs || 0) + (rec.grubHub || 0) + (rec.uberEats || 0);
                    saveDatabase();
                    renderApp();
                }
            });
        });

        // 2. Checkbox change listener
        row.querySelectorAll('.gig-no-earn').forEach(cb => {
            cb.addEventListener('change', (e) => {
                const date = e.target.dataset.date;
                const key = e.target.dataset.key;
                const checked = e.target.checked;
                
                const rec = state.deliveryEarnings.find(item => item.date === date);
                if (rec) {
                    const capKey = key.charAt(0).toUpperCase() + key.slice(1);
                    rec['noEarn' + capKey] = checked;
                    if (checked) {
                        rec[key] = 0;
                    }
                    rec.total = (rec.cash || 0) + (rec.sideGigs || 0) + (rec.grubHub || 0) + (rec.uberEats || 0);
                    saveDatabase();
                    renderApp();
                }
            });
        });

        // 3. Budget input listener
        const budgetInput = row.querySelector('.gig-budget-input');
        if (budgetInput) {
            budgetInput.addEventListener('change', (e) => {
                const date = e.target.dataset.date;
                const parsedVal = parseFormula(e.target.value);
                
                state.deliveryBudgets = state.deliveryBudgets || {};
                if (parsedVal > 0) {
                    state.deliveryBudgets[date] = parsedVal;
                } else {
                    delete state.deliveryBudgets[date];
                }
                saveDatabase();
                renderApp();
            });
        }

        // 4. Off-Day Reason listener
        const offDayInput = row.querySelector('.gig-off-day-input');
        if (offDayInput) {
            offDayInput.addEventListener('change', (e) => {
                const date = e.target.dataset.date;
                const val = e.target.value.trim();
                
                const rec = state.deliveryEarnings.find(item => item.date === date);
                if (rec) {
                    rec.offDayReason = val;
                    if (val) {
                        // Clear actual earnings and no-earn checkboxes
                        rec.cash = 0;
                        rec.sideGigs = 0;
                        rec.grubHub = 0;
                        rec.uberEats = 0;
                        rec.total = 0;
                        rec.noEarnCash = false;
                        rec.noEarnSideGigs = false;
                        rec.noEarnGrubHub = false;
                        rec.noEarnUberEats = false;
                    }
                    saveDatabase();
                    renderApp();
                }
            });
        }

        // 5. Day Off Toggle Checkbox
        const dayOffToggle = row.querySelector('.day-off-toggle');
        if (dayOffToggle) {
            dayOffToggle.addEventListener('change', (e) => {
                const date = e.target.dataset.date;
                const checked = e.target.checked;
                
                const rec = state.deliveryEarnings.find(item => item.date === date);
                if (rec) {
                    if (checked) {
                        rec.offDayReason = rec.offDayReason || 'Off-Day';
                        // Clear actual earnings and no-earn checkboxes
                        rec.cash = 0;
                        rec.cashFormula = '';
                        rec.sideGigs = 0;
                        rec.sideGigsFormula = '';
                        rec.grubHub = 0;
                        rec.grubHubFormula = '';
                        rec.uberEats = 0;
                        rec.uberEatsFormula = '';
                        rec.total = 0;
                        rec.noEarnCash = false;
                        rec.noEarnSideGigs = false;
                        rec.noEarnGrubHub = false;
                        rec.noEarnUberEats = false;
                    } else {
                        rec.offDayReason = '';
                    }
                    saveDatabase();
                    renderApp();
                }
            });
        }
        
        gridBody.appendChild(row);
    });
    
    renderDeliveryYearSummary();
    
    // Restore focus if a tab navigation was queued
    if (state.nextFocusDate && state.nextFocusKey) {
        const targetInput = document.querySelector(`textarea.gig-input[data-date="${state.nextFocusDate}"][data-key="${state.nextFocusKey}"]`);
        if (targetInput) {
            targetInput.focus();
            targetInput.select();
        }
        state.nextFocusDate = null;
        state.nextFocusKey = null;
    }
}

function getWeeksGroupedByMonth(year) {
    // Scan Dec 1 of previous year to Jan 31 of next year to cover boundaries
    const start = new Date(year - 1, 11, 1);
    const day = start.getDay();
    const diffToMonday = day === 0 ? -6 : 1 - day;
    const currentMonday = new Date(start);
    currentMonday.setDate(start.getDate() + diffToMonday);
    
    const end = new Date(year + 1, 0, 31);
    
    const grouped = {};
    MONTH_ORDER.forEach(m => grouped[m] = []);
    
    let safetyCounter = 0;
    while (currentMonday < end && safetyCounter < 100) {
        safetyCounter++;
        const week = [];
        for (let i = 0; i < 7; i++) {
            const date = new Date(currentMonday);
            date.setDate(currentMonday.getDate() + i);
            week.push(ensureDeliveryEarningForDate(date));
        }
        
        // Count days in each year-month
        const monthCounts = {};
        week.forEach(gRecord => {
            const dateObj = new Date(gRecord.date + 'T00:00:00');
            const dYear = dateObj.getFullYear();
            const dMonth = MONTH_ORDER[dateObj.getMonth()];
            const key = `${dYear}-${dMonth}`;
            monthCounts[key] = (monthCounts[key] || 0) + 1;
        });
        
        // Find majority year-month
        let maxKey = null;
        let maxCount = -1;
        for (const [k, count] of Object.entries(monthCounts)) {
            if (count > maxCount) {
                maxCount = count;
                maxKey = k;
            }
        }
        
        if (maxKey) {
            const [kYear, kMonth] = maxKey.split('-');
            if (parseInt(kYear) === year) {
                grouped[kMonth].push(week);
            }
        }
        
        currentMonday.setDate(currentMonday.getDate() + 7);
    }
    
    return grouped;
}

// Group delivery earnings into Mon-Sun weeks for a specific month using majority rule
function getDeliveryWeeksForMonth(month) {
    const grouped = getWeeksGroupedByMonth(state.currentYear);
    state.deliveryEarnings.sort((a, b) => a.date.localeCompare(b.date));
    return grouped[month] || [];
}

function renderLoansTab() {
    const listContainer = document.getElementById('loans-overview-grid');
    if (listContainer) listContainer.innerHTML = '';
    
    const tableBody = document.getElementById('loans-table-body');
    if (tableBody) tableBody.innerHTML = '';
    
    const filteredLoans = state.loans.filter(l => l.type === 'loan');
    
    filteredLoans.forEach((loan, idx) => {
        let progressPct = 0;
        let badgeText = '';
        let gaugeLabelsHtml = '';
        const paid = Math.max(0, loan.startBal - loan.currentBal);
        
        progressPct = loan.startBal > 0 ? (paid / loan.startBal) * 100 : 0;
        badgeText = `${progressPct.toFixed(0)}% Payoff`;
        gaugeLabelsHtml = `
            <span>Paid: $${paid.toFixed(0)}</span>
            <span>Goal: $${loan.startBal.toFixed(0)}</span>
        `;
        
        // Card overview
        const card = document.createElement('div');
        card.className = 'glass-card loan-overview-card';
        card.style.cursor = 'default';
        
        card.innerHTML = `
            <div class="loan-card-top">
                <h3 class="loan-card-title">${escapeHTML(loan.name)}</h3>
                <div style="display: flex; align-items: center; gap: 0.5rem;">
                    <span class="card-icon info" style="font-size:0.75rem;">${badgeText}</span>
                    <button class="action-btn small-btn outline-btn edit-loan-card-btn" data-id="${loan.id}" style="padding: 2px 6px; font-size: 0.75rem;">Edit</button>
                </div>
            </div>
            <div class="loan-progress-gauge">
                <div class="gauge-track">
                    <div class="gauge-fill" style="width: ${progressPct}%"></div>
                </div>
                <div class="gauge-labels">
                    ${gaugeLabelsHtml}
                </div>
            </div>
            <div class="loan-card-footer">
                <div>
                    <div class="loan-card-bal-label">Current Debt</div>
                    <div class="loan-card-bal-val">${formatCardBalance(loan.currentBal)}</div>
                </div>
                <div class="loan-card-payment">
                    <div class="loan-payment-label">Monthly Pmt</div>
                    <div class="loan-payment-val">$${loan.monthlyMin.toFixed(2)}</div>
                </div>
            </div>
            <div class="loan-card-action">
                <input type="number" placeholder="Amt" class="custom-input pay-amt-input" style="padding:0.4rem; font-size:0.8rem; width:80px;" id="pay-input-${loan.id}">
                <button class="action-btn small-btn solid-btn record-pay-btn" data-id="${loan.id}">Record Payment</button>
            </div>
        `;
        
        // Edit button listener inside card overview
        card.querySelector('.edit-loan-card-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            openEditLoanModal(loan.id);
        });
        
        // Record payment action listener
        card.querySelector('.record-pay-btn').addEventListener('click', (e) => {
            const id = e.target.dataset.id;
            const inputVal = parseFloat(document.getElementById(`pay-input-${id}`).value);
            
            if (isNaN(inputVal) || inputVal <= 0) return;
            
            const targetLoan = state.loans.find(l => l.id === id);
            if (targetLoan) {
                targetLoan.currentBal = Math.max(0, targetLoan.currentBal - inputVal);

                // Also add transaction to calendar on selectedDate
                const dObj = new Date(state.selectedDate + 'T00:00:00');
                const y = dObj.getFullYear();
                const mShort = MONTH_ORDER[dObj.getMonth()];
                const key = `${y}-${mShort}`;

                ensureYearMonthInitialized(y, mShort);

                const linkId = 'manual-pmt-' + Math.random().toString(36).substr(2, 9);

                state.personalCalendar[key].push({
                    id: 'p-' + Math.random().toString(36).substr(2, 9),
                    date: state.selectedDate,
                    description: `Pmt: ${targetLoan.name}`,
                    amount: -Math.abs(inputVal),
                    linkedPaymentId: linkId,
                    payoffTargetId: id
                });

                // Also add corresponding payment transaction inside the credit card/loan's calendar ledger!
                if (!state.cardCalendars) state.cardCalendars = {};
                if (!state.cardCalendars[id]) state.cardCalendars[id] = {};
                if (!state.cardCalendars[id][key]) state.cardCalendars[id][key] = [];

                state.cardCalendars[id][key].push({
                    id: 'c-' + Math.random().toString(36).substr(2, 9),
                    date: state.selectedDate,
                    description: "Payment from Personal",
                    amount: Math.abs(inputVal),
                    linkedPaymentId: linkId,
                    payoffTargetId: id
                });

                saveDatabase();
                renderApp();
                logSuccess(`Recorded $${inputVal.toFixed(2)} payment to ${targetLoan.name}! Saved in checking calendar.`);
            }
        });
        
        listContainer.appendChild(card);

        // Table row
        const row = document.createElement('tr');
        row.innerHTML = `
            <td><strong>${escapeHTML(loan.name)}</strong></td>
            <td>$${loan.startBal.toFixed(2)}</td>
            <td class="${loan.currentBal < 0 ? 'positive' : 'negative'} font-heading" style="font-weight:600;">${formatCardBalance(loan.currentBal)}</td>
            <td class="positive">$${paid.toFixed(2)}</td>
            <td>$${loan.monthlyMin.toFixed(2)}</td>
            <td><strong>${progressPct.toFixed(0)}%</strong></td>
            <td class="table-actions-cell" style="display:flex; gap:0.4rem; justify-content:flex-end;">
                <button class="action-btn small-btn outline-btn edit-loan-btn" data-id="${loan.id}">Edit</button>
                <button class="action-btn small-btn danger-btn delete-loan-btn" data-id="${loan.id}">Delete</button>
            </td>
        `;
        
        row.querySelector('.edit-loan-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            openEditLoanModal(loan.id);
        });
        
        row.querySelector('.delete-loan-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            const id = e.target.dataset.id;
            const index = state.loans.findIndex(l => l.id === id);
            if (index > -1) {
                const removed = state.loans.splice(index, 1)[0];
                syncMortgageLoansToAllMonths();
                saveDatabase();
                renderApp();
                logSystem(`Deleted debt target: ${removed.name}`);
            }
        });
        
        tableBody.appendChild(row);
    });
    
    if (filteredLoans.length === 0) {
        tableBody.innerHTML = `<tr><td colspan="7" class="muted-text" style="text-align:center;">No active installment loans. Click New Loan Target to add one.</td></tr>`;
    }
    renderProposedPaymentsList('loan', 'proposed-loan-payments-body');
}

function renderCreditCardsTab() {
    // Keep displayed balances in sync with the ledger so the overview grid doesn't show a stale
    // currentBal from before the user opened a specific card's own dashboard (which recomputes it).
    reconcileCardCurrentBalances();
    // If a CC sub-dashboard is currently active, ensure the sub-dashboard is shown and overview hidden
    if (state.ccSelectedCardId) {
        document.getElementById('creditcards-overview-layout').classList.add('hidden');
        document.getElementById('cc-dashboard-layout').classList.remove('hidden');
        renderCardDashboard(state.ccSelectedCardId);
        return;
    } else {
        document.getElementById('creditcards-overview-layout').classList.remove('hidden');
        document.getElementById('cc-dashboard-layout').classList.add('hidden');
    }

    const listContainer = document.getElementById('creditcards-overview-grid');
    if (listContainer) listContainer.innerHTML = '';
    
    const tableBody = document.getElementById('creditcards-table-body');
    if (tableBody) tableBody.innerHTML = '';
    
    const filteredLoans = state.loans.filter(l => l.type === 'credit');
    
    filteredLoans.forEach((loan, idx) => {
        let progressPct = 0;
        let badgeText = '';
        let gaugeLabelsHtml = '';
        const paid = Math.max(0, loan.startBal - loan.currentBal);
        
        if (loan.isChargeCard) {
            progressPct = 0;
            badgeText = 'Charge Card';
            gaugeLabelsHtml = `
                <span>Balance: $${loan.currentBal.toFixed(0)}</span>
                <span>No preset limit</span>
            `;
        } else {
            const limit = loan.limit || 5000;
            progressPct = Math.min(100, Math.max(0, (loan.currentBal / limit) * 100));
            badgeText = `${progressPct.toFixed(0)}% Used`;
            gaugeLabelsHtml = `
                <span>Used: $${loan.currentBal.toFixed(0)}</span>
                <span>Limit: $${limit.toFixed(0)}</span>
            `;
        }
        
        // Card overview
        const card = document.createElement('div');
        card.className = 'glass-card loan-overview-card';
        card.style.cursor = 'pointer';
        card.addEventListener('click', (e) => {
            if (e.target.closest('.loan-card-action') || e.target.closest('input') || e.target.closest('button')) {
                return;
            }
            state.ccSelectedCardId = loan.id;
            document.getElementById('creditcards-overview-layout').classList.add('hidden');
            document.getElementById('cc-dashboard-layout').classList.remove('hidden');
            renderCardDashboard(loan.id);
        });
        
        card.innerHTML = `
            <div class="loan-card-top">
                <h3 class="loan-card-title">${escapeHTML(loan.name)}</h3>
                <div style="display: flex; align-items: center; gap: 0.5rem;">
                    <span class="card-icon info" style="font-size:0.75rem;">${badgeText}</span>
                    <button class="action-btn small-btn outline-btn edit-loan-card-btn" data-id="${loan.id}" style="padding: 2px 6px; font-size: 0.75rem;">Edit</button>
                </div>
            </div>
            <div class="loan-progress-gauge">
                <div class="gauge-track">
                    <div class="gauge-fill" style="width: ${progressPct}%"></div>
                </div>
                <div class="gauge-labels">
                    ${gaugeLabelsHtml}
                </div>
            </div>
            <div class="loan-card-footer">
                <div>
                    <div class="loan-card-bal-label">Current Debt</div>
                    <div class="loan-card-bal-val">${formatCardBalance(loan.currentBal)}</div>
                </div>
                <div class="loan-card-payment">
                    <div class="loan-payment-label">Monthly Pmt</div>
                    <div class="loan-payment-val">$${loan.monthlyMin.toFixed(2)}</div>
                </div>
            </div>
            <div class="loan-card-action">
                <input type="number" placeholder="Amt" class="custom-input pay-amt-input" style="padding:0.4rem; font-size:0.8rem; width:80px;" id="pay-input-${loan.id}">
                <button class="action-btn small-btn solid-btn record-pay-btn" data-id="${loan.id}">Record Payment</button>
            </div>
        `;
        
        // Edit button listener inside card overview
        card.querySelector('.edit-loan-card-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            openEditLoanModal(loan.id);
        });
        
        // Record payment action listener
        card.querySelector('.record-pay-btn').addEventListener('click', (e) => {
            const id = e.target.dataset.id;
            const inputVal = parseFloat(document.getElementById(`pay-input-${id}`).value);
            
            if (isNaN(inputVal) || inputVal <= 0) return;
            
            const targetLoan = state.loans.find(l => l.id === id);
            if (targetLoan) {
                targetLoan.currentBal = Math.max(0, targetLoan.currentBal - inputVal);

                // Also add transaction to calendar on selectedDate
                const dObj = new Date(state.selectedDate + 'T00:00:00');
                const y = dObj.getFullYear();
                const mShort = MONTH_ORDER[dObj.getMonth()];
                const key = `${y}-${mShort}`;

                ensureYearMonthInitialized(y, mShort);

                const linkId = 'manual-pmt-' + Math.random().toString(36).substr(2, 9);

                state.personalCalendar[key].push({
                    id: 'p-' + Math.random().toString(36).substr(2, 9),
                    date: state.selectedDate,
                    description: `Pmt: ${targetLoan.name}`,
                    amount: -Math.abs(inputVal),
                    linkedPaymentId: linkId,
                    payoffTargetId: id
                });

                // Also add corresponding payment transaction inside the credit card/loan's calendar ledger!
                if (!state.cardCalendars) state.cardCalendars = {};
                if (!state.cardCalendars[id]) state.cardCalendars[id] = {};
                if (!state.cardCalendars[id][key]) state.cardCalendars[id][key] = [];

                state.cardCalendars[id][key].push({
                    id: 'c-' + Math.random().toString(36).substr(2, 9),
                    date: state.selectedDate,
                    description: "Payment from Personal",
                    amount: Math.abs(inputVal),
                    linkedPaymentId: linkId,
                    payoffTargetId: id
                });

                saveDatabase();
                renderApp();
                logSuccess(`Recorded $${inputVal.toFixed(2)} payment to ${targetLoan.name}! Saved in checking calendar.`);
            }
        });
        
        listContainer.appendChild(card);

        // Table row
        const row = document.createElement('tr');
        row.style.cursor = 'pointer';
        row.addEventListener('click', (e) => {
            if (e.target.closest('button') || e.target.closest('input')) {
                return;
            }
            state.ccSelectedCardId = loan.id;
            document.getElementById('creditcards-overview-layout').classList.add('hidden');
            document.getElementById('cc-dashboard-layout').classList.remove('hidden');
            renderCardDashboard(loan.id);
        });
        row.innerHTML = `
            <td><strong>${escapeHTML(loan.name)}</strong></td>
            <td>$${loan.startBal.toFixed(2)}</td>
            <td class="${loan.currentBal < 0 ? 'positive' : 'negative'} font-heading" style="font-weight:600;">${formatCardBalance(loan.currentBal)}</td>
            <td class="positive">$${paid.toFixed(2)}</td>
            <td>$${loan.monthlyMin.toFixed(2)}</td>
            <td><strong>${progressPct.toFixed(0)}%</strong></td>
            <td class="table-actions-cell" style="display:flex; gap:0.4rem; justify-content:flex-end;">
                <button class="action-btn small-btn outline-btn edit-loan-btn" data-id="${loan.id}">Edit</button>
                <button class="action-btn small-btn danger-btn delete-loan-btn" data-id="${loan.id}">Delete</button>
            </td>
        `;
        
        row.querySelector('.edit-loan-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            openEditLoanModal(loan.id);
        });
        
        row.querySelector('.delete-loan-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            const id = e.target.dataset.id;
            const index = state.loans.findIndex(l => l.id === id);
            if (index > -1) {
                const removed = state.loans.splice(index, 1)[0];
                saveDatabase();
                renderApp();
                logSystem(`Deleted credit card payoff target: ${removed.name}`);
            }
        });
        
        tableBody.appendChild(row);
    });
    
    if (filteredLoans.length === 0) {
        tableBody.innerHTML = `<tr><td colspan="7" class="muted-text" style="text-align:center;">No active credit cards. Click New Card Target to add one.</td></tr>`;
    }
    renderProposedPaymentsList('credit', 'proposed-payments-body');
}

function updateBalanceTransferModeFields() {
    const isExisting = document.getElementById('xfer-mode').value === 'existing';
    document.getElementById('xfer-source-group').classList.toggle('hidden', isExisting);
    document.getElementById('xfer-fee-group').classList.toggle('hidden', isExisting);
    document.getElementById('xfer-current-group').classList.toggle('hidden', !isExisting);
    document.getElementById('xfer-amount-label').textContent = isExisting ? 'Original Transfer Amount' : 'Transfer Amount';
    document.getElementById('btn-execute-xfer').textContent = isExisting ? 'Add Existing Transfer' : 'Execute New Transfer';
}

function recordExistingBalanceTransfer(targetId, originalAmount, currentBalance, rate, expDate, transferOwner) {
    const targetCard = state.loans.find(card => card.id === targetId);
    if (!targetCard) {
        alert('Save the card before adding an existing balance transfer.');
        return;
    }
    if (!targetCard.promos) targetCard.promos = [];
    targetCard.promos.push({
        id: 'xfer-' + Math.random().toString(36).substr(2, 9),
        amount: originalAmount,
        originalAmount,
        currentBalance,
        rate,
        expDate,
        isXfer: true,
        isExisting: true,
        transferOwner: transferOwner || '',
        xferFromId: ''
    });
    saveDatabase();
    renderApp();
    openEditLoanModal(targetId);
    logSuccess(`Recorded existing balance transfer with $${currentBalance.toFixed(2)} remaining.`);
}

function renderBalanceTransfers(card) {
    const list = document.getElementById('loan-xfer-list');
    if (!list) return;
    const transfers = (card.promos || []).filter(item => item.isXfer);
    list.innerHTML = transfers.length ? transfers.map(item => {
        const original = Number(item.originalAmount ?? item.amount) || 0;
        const current = Number(item.currentBalance ?? item.amount) || 0;
        const source = item.xferFromId ? state.loans.find(loan => loan.id === item.xferFromId)?.name : '';
        const person = item.transferOwner === 'jason' ? 'Jason' : item.transferOwner === 'asia' ? 'Asia' : 'Not recorded';
        return `<div class="payment-plan-row"><span><strong>${item.isExisting ? 'Existing' : 'New'} balance transfer</strong> - $${current.toFixed(2)} remaining of $${original.toFixed(2)} | ${Number(item.rate || 0).toFixed(2)}% APR | Expires ${item.expDate || '-'}${source ? ` | From ${escapeHTML(source)}` : ''} <span class="cc-owner-badge ${item.transferOwner || 'unknown'}">By: ${person}</span></span></div>`;
    }).join('') : '<span class="muted-text">No balance transfers recorded.</span>';
}
function executeBalanceTransfer(targetId, sourceId, amount, feePct, rate, expDate, transferOwner) {
    if (isNaN(amount) || amount <= 0) {
        logError("Please enter a valid transfer amount.");
        return;
    }
    
    const targetCard = state.loans.find(l => l.id === targetId);
    const sourceCard = state.loans.find(l => l.id === sourceId);
    
    if (!targetCard || !sourceCard) {
        logError("Invalid target or source account selected.");
        return;
    }
    
    const feeAmount = amount * (feePct / 100);
    const totalAdded = amount + feeAmount;
    
    // Adjust balances
    sourceCard.currentBal = Math.max(0, sourceCard.currentBal - amount);
    targetCard.currentBal += totalAdded;
    
    // Log transactions on the target card
    const dObj = new Date(state.selectedDate + 'T00:00:00');
    const y = dObj.getFullYear();
    const mShort = MONTH_ORDER[dObj.getMonth()];
    const key = `${y}-${mShort}`;
    
    if (!state.cardCalendars) state.cardCalendars = {};
    if (!state.cardCalendars[targetId]) state.cardCalendars[targetId] = {};
    if (!state.cardCalendars[targetId][key]) state.cardCalendars[targetId][key] = [];
    
    // Add charge on target card
    state.cardCalendars[targetId][key].push({
        id: 'c-' + Math.random().toString(36).substr(2, 9),
        date: state.selectedDate,
        description: `Bal Transfer from ${sourceCard.name} (inc. ${feePct}% fee)`,
        owner: transferOwner || 'personal',
        balanceTransferBy: transferOwner || '',
        amount: -Math.abs(totalAdded)
    });
    
    // Log transaction on source card if it's a credit card
    if (sourceCard.type === 'credit') {
        if (!state.cardCalendars[sourceId]) state.cardCalendars[sourceId] = {};
        if (!state.cardCalendars[sourceId][key]) state.cardCalendars[sourceId][key] = [];
        
        state.cardCalendars[sourceId][key].push({
            id: 'c-' + Math.random().toString(36).substr(2, 9),
            date: state.selectedDate,
            description: `Bal Transfer to ${targetCard.name}`,
            owner: transferOwner || 'personal',
            balanceTransferBy: transferOwner || '',
            amount: Math.abs(amount)
        });
    }
    
    // Add promo balance item
    if (!targetCard.promos) targetCard.promos = [];
    targetCard.promos.push({
        id: Math.random().toString(36).substr(2, 9),
        amount: totalAdded,
        originalAmount: amount,
        currentBalance: totalAdded,
        rate: rate,
        expDate: expDate,
        isXfer: true,
        transferOwner: transferOwner || '',
        xferFromId: sourceId
    });
    
    saveDatabase();
    renderApp();
    
    // Re-populate modal view
    openEditLoanModal(targetId);
    
    logSuccess(`Successfully executed balance transfer of $${amount.toFixed(2)} from ${sourceCard.name} to ${targetCard.name}! Charged $${totalAdded.toFixed(2)} (with $${feeAmount.toFixed(2)} fee) at ${rate}% APR promo interest rate.`);
}

// Renders the "Proposed Future Payments" table for either credit cards or installment loans.
// `type` filters state.loans so loan payments don't leak into the Credit Cards tab (and vice versa) —
// each tab gets its own table body / dialog context via `bodyId`.
function renderProposedPaymentsList(type, bodyId) {
    const body = document.getElementById(bodyId);
    if (!body) return;
    body.innerHTML = '';

    const propPays = [];

    // Resolve the target card/loan for a "Pmt: " transaction, preferring the stable payoffTargetId
    // link over parsing the name back out of the description (which breaks if renamed), and
    // restricted to the requested type so credit-card and loan payments stay in their own tables.
    const resolvePaymentTargetCard = (tx) => {
        if (tx.payoffTargetId) {
            const byId = state.loans.find(l => l.id === tx.payoffTargetId && l.type === type);
            if (byId) return byId;
        }
        const cardName = tx.description.replace('Pmt: ', '');
        return state.loans.find(l => l.name === cardName && l.type === type) || null;
    };

    // 1. Scan Personal Checking Calendar
    if (state.personalCalendar) {
        for (const [key, txList] of Object.entries(state.personalCalendar)) {
            txList.forEach(tx => {
                if (tx.description && tx.description.startsWith('Pmt: ')) {
                    const matchingCard = resolvePaymentTargetCard(tx);
                    if (matchingCard) {
                        propPays.push({
                            id: tx.id,
                            date: tx.date,
                            source: 'Personal Checking',
                            sourceType: 'personal',
                            targetId: matchingCard.id,
                            targetName: matchingCard.name,
                            amount: Math.abs(tx.amount),
                            checkingTxId: tx.id,
                            linkId: tx.linkedPaymentId || '',
                            monthKey: key,
                            isAutomatic: !!tx.isAutomaticCardPayment
                        });
                    }
                }
            });
        }
    }

    // 2. Scan Joint Checking Register
    if (state.jointRegister) {
        state.jointRegister.forEach(tx => {
            if (tx.description && tx.description.startsWith('Pmt: ')) {
                const matchingCard = resolvePaymentTargetCard(tx);
                if (matchingCard) {
                    propPays.push({
                        id: tx.id,
                        date: tx.date,
                        source: 'Joint Checking',
                        sourceType: 'joint',
                        targetId: matchingCard.id,
                        targetName: matchingCard.name,
                        amount: Math.abs(tx.amount),
                        checkingTxId: tx.id,
                        linkId: tx.linkedPaymentId || '',
                        isAutomatic: !!tx.isAutomaticCardPayment
                    });
                }
            }
        });
    }
    
    propPays.sort((a, b) => new Date(a.date).getTime() - new Date(b.date).getTime());
    
    propPays.forEach(pay => {
        const row = document.createElement('tr');
        const actionsHtml = pay.isAutomatic
            ? `<button class="action-btn small-btn outline-btn auto-pay-guard-btn" data-target="${pay.targetId}">Managed automatically</button>`
            : `<button class="action-btn small-btn outline-btn edit-prop-pay-btn" data-id="${pay.id}" data-source="${pay.sourceType}" data-target="${pay.targetId}" data-date="${pay.date}" data-amount="${pay.amount}" data-link-id="${pay.linkId}" data-month-key="${pay.monthKey || ''}">Edit</button>
                <button class="action-btn small-btn danger-btn delete-prop-pay-btn" data-id="${pay.id}" data-source="${pay.sourceType}" data-target="${pay.targetId}" data-date="${pay.date}" data-amount="${pay.amount}" data-link-id="${pay.linkId}">Delete</button>`;
        row.innerHTML = `
            <td><strong>${pay.date}</strong></td>
            <td><span class="card-icon ${pay.sourceType === 'joint' ? 'success' : 'info'}" style="font-size:0.75rem; padding: 2px 6px;">${pay.source}</span></td>
            <td>${type === 'loan' ? 'Loan' : 'Card'}: ${escapeHTML(pay.targetName)}</td>
            <td class="positive font-heading" style="font-weight:600;">$${pay.amount.toFixed(2)}</td>
            <td style="display:flex; gap:0.4rem; justify-content:flex-end;">
                ${actionsHtml}
            </td>
        `;

        if (pay.isAutomatic) {
            row.querySelector('.auto-pay-guard-btn').addEventListener('click', (e) => {
                e.stopPropagation();
                const targetName = state.loans.find(l => l.id === e.target.dataset.target)?.name || (type === 'loan' ? 'this loan' : 'this card');
                const sectionLabel = type === 'loan' ? "Installment Loans" : "Credit Cards";
                if (confirm(`Automatic payments can't be edited or deleted here. For a one-time change, edit the transaction directly in the Personal or Joint ledger. To change it permanently, adjust ${targetName}'s payment strategy under ${sectionLabel}.\n\nGo there now?`)) {
                    goToCardPaymentInCreditCards(e.target.dataset.target, pay.date);
                }
            });
            body.appendChild(row);
            return;
        }

        row.querySelector('.edit-prop-pay-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            const btn = e.target;
            document.getElementById('proposed-payment-form').reset();
            document.getElementById('prop-pay-action').value = 'edit';
            document.getElementById('prop-pay-edit-id').value = btn.dataset.id;
            document.getElementById('prop-pay-link-id').value = btn.dataset.linkId || '';
            document.getElementById('prop-pay-date').value = btn.dataset.date;
            document.getElementById('prop-pay-source').value = btn.dataset.source;
            document.getElementById('prop-pay-amount').value = btn.dataset.amount;
            document.getElementById('prop-pay-type').value = type;
            // Populate targets dropdown, restricted to this table's type (credit or loan)
            const select = document.getElementById('prop-pay-target');
            select.innerHTML = '';
            state.loans.filter(card => card.type === type).forEach(card => {
                const opt = document.createElement('option');
                opt.value = card.id;
                opt.textContent = card.name;
                select.appendChild(opt);
            });
            select.value = btn.dataset.target;
            document.querySelector('#proposed-payment-form h3').textContent = 'Edit Proposed Payment';
            document.querySelector('#proposed-payment-form button[type="submit"]').textContent = 'Update Payment';
            document.getElementById('proposed-payment-dialog').showModal();
        });

        row.querySelector('.delete-prop-pay-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            if (confirm("Are you sure you want to delete this proposed payment? This will remove the transaction from both checking and card calendars.")) {
                const { id, source, target, date, amount, linkId } = e.target.dataset;
                const amt = parseFloat(amount);

                // 1. Delete from checking account
                if (source === 'personal') {
                    for (const [key, txList] of Object.entries(state.personalCalendar)) {
                        const idx = txList.findIndex(tx => tx.id === id);
                        if (idx > -1) {
                            txList.splice(idx, 1);
                            break;
                        }
                    }
                } else if (source === 'joint') {
                    const idx = state.jointRegister.findIndex(tx => tx.id === id);
                    if (idx > -1) {
                        state.jointRegister.splice(idx, 1);
                    }
                }

                // 2. Delete from credit card calendar. Prefer the stable linkedPaymentId set at creation
                // time; only fall back to the date+amount heuristic for legacy entries that predate it,
                // since the heuristic can match the wrong row when two payments share a date and amount.
                const dateObj = new Date(date + 'T00:00:00');
                const y = dateObj.getFullYear();
                const mShort = MONTH_ORDER[dateObj.getMonth()];
                const cKey = `${y}-${mShort}`;

                if (state.cardCalendars && state.cardCalendars[target] && state.cardCalendars[target][cKey]) {
                    const ccList = state.cardCalendars[target][cKey];
                    const ccIdx = linkId
                        ? ccList.findIndex(tx => tx.linkedPaymentId === linkId)
                        : ccList.findIndex(tx => tx.date === date && Math.abs(tx.amount - amt) < 0.01 && tx.description.startsWith('Payment from'));
                    if (ccIdx > -1) {
                        ccList.splice(ccIdx, 1);
                    }
                }

                // 3. Re-adjust balance
                const cardObj = state.loans.find(l => l.id === target);
                if (cardObj) {
                    cardObj.currentBal += amt;
                }
                
                saveDatabase();
                renderApp();
                logSystem(`Deleted proposed payment: $${amt.toFixed(2)} to ${cardObj ? cardObj.name : target}`);
            }
        });
        
        body.appendChild(row);
    });
    
    if (propPays.length === 0) {
        body.innerHTML = '<tr><td colspan="5" class="muted-text" style="text-align:center;">No proposed future payments scheduled.</td></tr>';
    }
}

// --- UTILS & LOGS ---
function logSystem(msg) {
    const container = document.getElementById('logs-container');
    if (!container) return;
    const entry = document.createElement('div');
    entry.className = 'log-entry system';
    entry.textContent = `[SYSTEM]: ${msg}`;
    container.appendChild(entry);
    container.scrollTop = container.scrollHeight;
}

function logSuccess(msg) {
    const container = document.getElementById('logs-container');
    if (!container) return;
    const entry = document.createElement('div');
    entry.className = 'log-entry success';
    entry.textContent = `[SUCCESS]: ${msg}`;
    container.appendChild(entry);
    container.scrollTop = container.scrollHeight;
}

function updateQuickAddFormFields() {
    const isPersonal = state.dashboardType === 'personal';
    const isJoint = state.dashboardType === 'joint';
    const isSavingsTransfer = isPersonal && document.getElementById('personal-trans-type').value === 'savings-transfer';
    const isContribution = isJoint && document.getElementById('joint-trans-type').value === 'contribution';
    const isWithdrawal = isContribution && document.getElementById('contribution-direction').value === 'withdrawal';
    
    const payrollBtn = document.getElementById('btn-configure-payroll');
    if (payrollBtn) {
        payrollBtn.classList.toggle('hidden', !isPersonal);
    }
    
    document.getElementById('personal-type-group').classList.toggle('hidden', !isPersonal);
    document.getElementById('trans-amount-label').textContent = isSavingsTransfer ? 'Personal Account Amount' : 'Amount';
    document.getElementById('trans-amount-hint').classList.toggle('hidden', !isSavingsTransfer);
    document.getElementById('trans-amount').placeholder = isSavingsTransfer ? 'Negative to move into Savings' : 'Negative for expenses';
    document.getElementById('joint-contribution-group').classList.toggle('hidden', !isContribution);
    document.getElementById('single-amount-group').classList.toggle('hidden', isContribution);
    document.getElementById('contribution-deposit-fields').classList.toggle('hidden', isWithdrawal);
    document.getElementById('contribution-recipient-group').classList.toggle('hidden', !isWithdrawal);
    document.getElementById('contribution-withdrawal-field').classList.toggle('hidden', !isWithdrawal);
    document.getElementById('trans-amount').required = !isContribution;
    document.getElementById('trans-jason-amount').required = isContribution && !isWithdrawal;
    document.getElementById('trans-asia-amount').required = isContribution && !isWithdrawal;
    document.getElementById('contribution-withdrawal-amount').required = isWithdrawal;
}

function updateTabTitles() {
    const activeTab = document.querySelector('.nav-btn.active').dataset.tab;
    const title = document.getElementById('current-tab-title');
    const subtitle = document.getElementById('current-tab-subtitle');
    
    if (activeTab === 'dashboard') {
        let accountName = 'Personal';
        if (state.dashboardType === 'joint') {
            accountName = 'Joint';
        } else if (state.dashboardType !== 'personal') {
            const card = state.loans.find(l => l.id === state.dashboardType);
            if (card) accountName = card.name;
        }
        title.textContent = `${accountName} Dashboard`;
        subtitle.textContent = `${state.dashboardType === 'personal' ? 'Personal checking calendar and cash flows' : (state.dashboardType === 'joint' ? 'Shared Joint Account ledger and expenditures' : 'Credit card transactions and running balance')}`;
    } else if (activeTab === 'bills') {
        title.textContent = `Shared Bills Split`;
        subtitle.textContent = "Split monthly payments and track delivery allocations";
    } else if (activeTab === 'delivery') {
        title.textContent = `Delivery Side Gigs`;
        subtitle.textContent = "Log gig app logs and calculate daily payouts";
    } else if (activeTab === 'savings') {
        title.textContent = 'Savings Tracker';
        subtitle.textContent = 'Plan savings transfers and track the projected balance';
    } else if (activeTab === 'loans') {
        title.textContent = 'Installment Loans';
        subtitle.textContent = 'Debt payoff targets, escrow, and installment target options';
    } else if (activeTab === 'creditcards') {
        title.textContent = state.ccSelectedCardId ? 'Credit Card Dashboard' : 'Credit Cards';
        subtitle.textContent = state.ccSelectedCardId ? 'Transaction calendar and ledger' : 'Credit card payoff targets and promotions';
    } else if (activeTab === 'billtracker') {
        title.textContent = 'Bill Settings';
        subtitle.textContent = 'Setup recurring charges, statement/payment dates, and checking/card sync';
    }
}

function populateCCDropdowns() {
    const dashboardCC = document.getElementById('dashboard-cc-optgroup');
    const billSourceCC = document.getElementById('bill-source-cc-optgroup');
    const billSettingsSourceCC = document.getElementById('bill-settings-source-cc-optgroup');
    
    if (dashboardCC) dashboardCC.innerHTML = '';
    if (billSourceCC) billSourceCC.innerHTML = '';
    if (billSettingsSourceCC) billSettingsSourceCC.innerHTML = '';
    
    state.loans.forEach(loan => {
        if (loan.type !== 'credit') return;
        const opt = document.createElement('option');
        opt.value = loan.id;
        opt.textContent = loan.name;
        
        if (dashboardCC) dashboardCC.appendChild(opt.cloneNode(true));
        if (billSourceCC) billSourceCC.appendChild(opt.cloneNode(true));
        if (billSettingsSourceCC) billSettingsSourceCC.appendChild(opt.cloneNode(true));
    });
}

function countWeekdayOccurrences(year, month, weekday) {
    const monthIndex = MONTH_ORDER.indexOf(month);
    const daysInMonth = new Date(year, monthIndex + 1, 0).getDate();
    let count = 0;
    for (let day = 1; day <= daysInMonth; day++) if (new Date(year, monthIndex, day).getDay() === weekday) count++;
    return count;
}

function getBillOccurrenceDates(rawBill, year, month) {
    // Day-level end date: no occurrences past it (recurringEndMonth already stops later months at
    // month granularity; this trims occurrences within the final month itself).
    const endDateFilter = dates => {
        let filtered = rawBill.recurringStartDate ? dates.filter(d => d >= rawBill.recurringStartDate) : dates;
        if (rawBill.recurringEndDate) filtered = filtered.filter(d => d <= rawBill.recurringEndDate);
        return filtered;
    };
    const legacyFrequency = ['weekly','biweekly','fourweekly','quarterly','annual'].includes(rawBill.budgetFrequency) ? rawBill.budgetFrequency : 'monthly';
    const frequency = rawBill.chargeFrequency || legacyFrequency;
    const monthIndex = MONTH_ORDER.indexOf(month);
    if (monthIndex < 0) return [];
    if (frequency === 'monthly') return endDateFilter([getBillChargeDate(year, month, rawBill.dueDay)]);

    let anchor = rawBill.frequencyStartDate ? new Date(rawBill.frequencyStartDate + 'T00:00:00') : null;
    if (!anchor || Number.isNaN(anchor.getTime())) {
        anchor = new Date(year, monthIndex, 1);
        const legacyDay = Number.isFinite(Number(rawBill.weeklyDay)) ? Number(rawBill.weeklyDay) : anchor.getDay();
        while (anchor.getDay() !== legacyDay) anchor.setDate(anchor.getDate() + 1);
    }
    const monthStart = new Date(year, monthIndex, 1);
    const monthEnd = new Date(year, monthIndex + 1, 0);
    if (anchor > monthEnd) return [];

    if (frequency === 'quarterly' || frequency === 'annual') {
        const intervalMonths = frequency === 'quarterly' ? 3 : 12;
        const difference = (year - anchor.getFullYear()) * 12 + monthIndex - anchor.getMonth();
        if (difference < 0 || difference % intervalMonths !== 0) return [];
        const day = Math.min(anchor.getDate(), monthEnd.getDate());
        return endDateFilter([formatLocalDate(new Date(year, monthIndex, day))]);
    }

    const intervalDays = frequency === 'biweekly' ? 14 : frequency === 'fourweekly' ? 28 : 7;
    const occurrence = new Date(anchor);
    while (occurrence < monthStart) occurrence.setDate(occurrence.getDate() + intervalDays);
    const dates = [];
    while (occurrence <= monthEnd) {
        dates.push(formatLocalDate(occurrence));
        occurrence.setDate(occurrence.getDate() + intervalDays);
    }
    return endDateFilter(dates);
}

function calculateBillFundingAmount(rawBill, year, month) {
    const chargeAmount = Math.max(0, Number(rawBill.frequencyAmount ?? rawBill.weeklyAmount ?? rawBill.budgetAmount) || 0);
    const chargeFrequency = rawBill.chargeFrequency || (['weekly','biweekly','fourweekly','quarterly','annual'].includes(rawBill.budgetFrequency) ? rawBill.budgetFrequency : 'monthly');
    const budgetMethod = rawBill.budgetFrequency === 'monthly' && rawBill.chargeFrequency ? 'monthly' : (rawBill.budgetFrequency === 'charge' ? 'charge' : rawBill.chargeFrequency ? rawBill.budgetFrequency : 'charge');
    let amount;
    if (budgetMethod === 'monthly') {
        const monthlyFactors = { monthly: 1, weekly: 52 / 12, biweekly: 26 / 12, fourweekly: 13 / 12, quarterly: 1 / 3, annual: 1 / 12 };
        amount = chargeAmount * (monthlyFactors[chargeFrequency] || 1);
    } else {
        amount = chargeAmount * getBillOccurrenceDates(rawBill, year, month).length;
    }
    return Math.round(amount * 100) / 100;
}

function recalculateBillBudgetForPeriod(rawBill, year, month, cycleKey = 'cycle1st') {
    const bill = normalizeBillSplitterItem(rawBill, cycleKey);
    const occurrenceDates = getBillOccurrenceDates(bill, year, month);
    bill.weeklyOccurrences = occurrenceDates.length;
    bill.occurrenceDates = occurrenceDates;
    bill.budgetAmount = calculateBillFundingAmount(bill, year, month);
    bill.amount = -bill.budgetAmount;
    if (bill.entryType === 'actual') bill.paymentAmount = Math.round(bill.occurrencePaymentAmount * occurrenceDates.length * 100) / 100;
    return bill;
}
function getBillRecurrenceMonthIndex(value) {
    const match = /^(\d{4})-(\d{2})$/.exec(value || '');
    if (!match) return null;
    return Number(match[1]) * 12 + Number(match[2]) - 1;
}

function getPeriodMonthIndex(year, month) {
    return Number(year) * 12 + MONTH_ORDER.indexOf(month);
}

function isBillActiveForPeriod(bill, year, month) {
    if (!bill.isRecurring) return true;
    const periodIndex = getPeriodMonthIndex(year, month);
    const startIndex = getBillRecurrenceMonthIndex(bill.recurringStartMonth);
    const endIndex = getBillRecurrenceMonthIndex(bill.recurringEndMonth);
    const withinRecurringRange = (startIndex === null || periodIndex >= startIndex) && (endIndex === null || periodIndex <= endIndex);
    if (!withinRecurringRange) return false;
    return bill.budgetFrequency === 'monthly' || getBillOccurrenceDates(bill, year, month).length > 0;
}

function normalizeBillSplitterItem(bill, cycleKey = 'cycle1st') {
    const budgetAmount = Math.abs(Number(bill.budgetAmount ?? bill.amount) || 0);
    const paymentAmount = Math.abs(Number(bill.paymentAmount ?? bill.amount) || 0);
    const isActual = (bill.entryType || 'actual') === 'actual';
    return {
        ...bill,
        id: bill.id || 'bill-' + Math.random().toString(36).substr(2, 9),
        account: bill.account || bill.name || 'Bill',
        category: ['bill','expense','utility','savings'].includes(bill.category) ? bill.category : 'bill',
        budgetAmount,
        paymentAmount: isActual ? paymentAmount : 0,
        samePaymentAmount: bill.samePaymentAmount ?? Math.abs(budgetAmount - paymentAmount) < 0.001,
        amount: -budgetAmount,
        dueDay: isActual ? Math.min(31, Math.max(1, Number(bill.dueDay) || (cycleKey === 'cycle1st' ? 1 : 15))) : 0,
        paymentSource: bill.paymentSource || 'jointChecking',
        entryType: bill.entryType || 'actual',
        ownership: bill.ownership || 'joint',
        cycleAllocation: bill.cycleAllocation || (cycleKey === 'cycle15th' ? '15th' : '1st'),
        budgetFrequency: bill.chargeFrequency === 'monthly' ? 'monthly' : (['weekly','biweekly','fourweekly','quarterly','annual'].includes(bill.chargeFrequency) ? 'charge' : (bill.budgetFrequency || 'monthly')),
        chargeFrequency: bill.chargeFrequency || (['weekly','biweekly','fourweekly','quarterly','annual'].includes(bill.budgetFrequency) ? bill.budgetFrequency : 'monthly'),
        frequencyAmount: Math.max(0, Number(bill.frequencyAmount ?? bill.weeklyAmount ?? budgetAmount) || 0),
        frequencyStartDate: bill.frequencyStartDate || '',
        occurrencePaymentAmount: Math.max(0, Number(bill.occurrencePaymentAmount ?? paymentAmount) || 0),
        weeklyAmount: Math.max(0, Number(bill.frequencyAmount ?? bill.weeklyAmount) || 0),
        weeklyDay: Number.isFinite(Number(bill.weeklyDay)) ? Number(bill.weeklyDay) : 6,
        weeklyOccurrences: Math.max(0, Number(bill.weeklyOccurrences) || 0),
        isRecurring: !!bill.isRecurring,
        recurringSeriesId: bill.recurringSeriesId || '',
        recurringStartMonth: bill.recurringStartMonth || '',
        recurringEndMonth: bill.recurringEndMonth || ''
    };
}

function restoreOrphanedPersonalRecurringBills() {
    const currentKey = `${state.currentYear}-${state.currentMonth}`;
    const currentBills = state.monthlyBills?.[currentKey];
    const existingAccounts = new Set(['cycle1st', 'cycle15th'].flatMap(cycleKey =>
        (currentBills?.[cycleKey]?.bills || []).map(bill => (bill.account || bill.name || '').trim().toLowerCase())
    ));
    const groups = new Map();
    Object.values(state.personalCalendar || {}).forEach(list => (list || []).forEach(tx => {
        const account = (tx.description || '').trim();
        const amount = Math.abs(Number(tx.amount) || 0);
        if (!account || amount <= 0 || !tx.isRecurring || tx.linkedBillId) return;
        const key = `${account.toLowerCase()}|${amount.toFixed(2)}`;
        if (!groups.has(key)) groups.set(key, { account, amount, entries: [] });
        groups.get(key).entries.push(tx);
    }));

    let restored = 0;
    groups.forEach(group => {
        if (existingAccounts.has(group.account.toLowerCase())) return;
        group.entries.sort((a, b) => a.date.localeCompare(b.date));
        const first = group.entries[0];
        const [year, monthNumber, day] = first.date.split('-').map(Number);
        const month = MONTH_ORDER[monthNumber - 1];
        const key = `${year}-${month}`;
        if (!month || !state.monthlyBills?.[key]) return;
        const cycleKey = 'cycle1st';
        const seriesId = `restored-personal-${Math.random().toString(36).substr(2, 9)}`;
        const bill = normalizeBillSplitterItem({
            id: seriesId,
            recurringSeriesId: seriesId,
            account: group.account,
            category: 'expense',
            budgetAmount: group.amount,
            paymentAmount: group.amount,
            occurrencePaymentAmount: group.amount,
            frequencyAmount: group.amount,
            samePaymentAmount: true,
            dueDay: day,
            paymentSource: 'personalChecking',
            entryType: 'actual',
            ownership: 'personal',
            cycleAllocation: '1st',
            budgetFrequency: 'monthly',
            chargeFrequency: 'monthly',
            isRecurring: true,
            recurringStartMonth: first.date.slice(0, 7),
            recurringEndMonth: ''
        }, cycleKey);
        state.monthlyBills[key][cycleKey].bills.push(bill);
        syncBillLedgerEntry(bill, year, month);
        propagateRecurringBillChanges(bill, year, month);
        existingAccounts.add(group.account.toLowerCase());
        restored += 1;
    });
    return restored;
}
function recalculateBillCycleTotals(mBills) {
    const allBills = ['cycle1st', 'cycle15th'].flatMap(cycleKey => (mBills[cycleKey]?.bills || []).map(bill => normalizeBillSplitterItem(bill, cycleKey)));
    ['cycle1st', 'cycle15th'].forEach(cycleKey => {
        const cycle = mBills[cycleKey];
        if (!cycle) return;
        cycle.totals = cycle.totals || {};
        cycle.totals.billsTotal = allBills.reduce((sum, bill) => {
            if (bill.cycleAllocation === 'both') return sum + bill.budgetAmount / 2;
            const assigned = bill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st';
            return sum + (assigned === cycleKey ? bill.budgetAmount : 0);
        }, 0);
    });
}

function propagateRecurringBillChanges(editedBill, year, month, previousBill = null) {
    const seriesId = editedBill.recurringSeriesId || editedBill.id;
    const currentIndex = year * 12 + MONTH_ORDER.indexOf(month);
    const requestedStartIndex = getBillRecurrenceMonthIndex(editedBill.recurringStartMonth);
    const requestedEndIndex = getBillRecurrenceMonthIndex(editedBill.recurringEndMonth);
    if (!state.billRecurrenceTemplates) state.billRecurrenceTemplates = {};
    if (!state.billRecurrenceStops) state.billRecurrenceStops = {};

    if (editedBill.isRecurring) {
        editedBill.recurringSeriesId = seriesId;
        delete state.billRecurrenceStops[seriesId];
        state.billRecurrenceTemplates[seriesId] = {
            bill: normalizeBillSplitterItem({ ...editedBill, recurringSeriesId: seriesId }),
            cycleKey: editedBill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st',
            startIndex: requestedStartIndex ?? currentIndex,
            endIndex: requestedEndIndex
        };
    } else {
        state.billRecurrenceStops[seriesId] = currentIndex + 1;
        delete state.billRecurrenceTemplates[seriesId];
    }

    Object.entries(state.monthlyBills || {}).forEach(([key, monthData]) => {
        const [keyYear, keyMonth] = key.split('-');
        const periodIndex = Number(keyYear) * 12 + MONTH_ORDER.indexOf(keyMonth);
        if (periodIndex <= currentIndex) return;
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            const list = monthData?.[cycleKey]?.bills || [];
            for (let i = list.length - 1; i >= 0; i--) {
                const candidate = normalizeBillSplitterItem(list[i], cycleKey);
                const sameSeries = (candidate.recurringSeriesId || candidate.id) === seriesId;
                const sameLegacyBill = previousBill && getBillLegacyRecurrenceKey(candidate) === getBillLegacyRecurrenceKey(previousBill);
                if (!sameSeries && !sameLegacyBill) continue;
                removeBillLedgerEntries(candidate.id, Number(keyYear), keyMonth, candidate);
                list.splice(i, 1);
            }
        });
        if (editedBill.isRecurring && isBillActiveForPeriod(editedBill, Number(keyYear), keyMonth)) {
            const targetCycle = editedBill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st';
            const futureBill = recalculateBillBudgetForPeriod({ ...editedBill, id: `${seriesId}-${keyYear}-${keyMonth}`, recurringSeriesId: seriesId }, Number(keyYear), keyMonth, targetCycle);
            monthData[targetCycle].bills.push(futureBill);
            syncBillLedgerEntry(futureBill, Number(keyYear), keyMonth);
        }
        recalculateBillCycleTotals(monthData);
    });
}
function getBillChargeDate(year, month, dueDay) {
    const monthIndex = MONTH_ORDER.indexOf(month);
    const lastDay = new Date(year, monthIndex + 1, 0).getDate();
    const day = Math.min(lastDay, Math.max(1, Number(dueDay) || 1));
    return `${year}-${String(monthIndex + 1).padStart(2, '0')}-${String(day).padStart(2, '0')}`;
}

function getBillOccurrencePaymentAmount(bill) {
    return Math.abs(Number(bill.occurrencePaymentAmount) || 0);
}

function getBillLinkedLedgerEntries(billId) {
    const entries = [];
    Object.values(state.personalCalendar || {}).forEach(list => entries.push(...(list || []).filter(tx => tx.linkedBillId === billId)));
    entries.push(...(state.jointRegister || []).filter(tx => tx.linkedBillId === billId));
    Object.values(state.cardCalendars || {}).forEach(calendar => Object.values(calendar || {}).forEach(list => entries.push(...(list || []).filter(tx => tx.linkedBillId === billId))));
    return entries;
}

// `force` widens what gets removed (legacy/mismatched entries). `purgeOverrides` additionally removes
// entries the user has individually edited or deleted (billOccurrenceOverridden/billOccurrenceDeleted).
// It defaults to `force` so full-purge callers (deleting the bill or its master setting) behave as before,
// but regeneration syncs must pass `purgeOverrides: false` — those flagged entries are the user's
// per-occurrence customizations, and wiping them made every edit/delete silently regenerate on the
// next render.
function removeBillLedgerEntries(billId, year, month, oldBill = null, force = false, purgeOverrides = force) {
    const key = `${year}-${month}`;
    // Use the real calendar date/month here, not state.currentYear/currentMonth (see the same fix in
    // syncBillLedgerEntry/syncBillTrackerBillsToAllMonths above).
    const todayStr = formatLocalDate(new Date());
    const today = new Date();
    const isRealCurrentMonth = year === today.getFullYear() && MONTH_ORDER.indexOf(month) === today.getMonth();
    const monthIndex = MONTH_ORDER.indexOf(month);
    const targetMonthPrefix = monthIndex >= 0 ? `${year}-${String(monthIndex + 1).padStart(2, '0')}-` : null;

    const expectedDates = oldBill ? getBillOccurrenceDates(oldBill, year, month) : [];
    const expectedAmount = oldBill ? -getBillOccurrencePaymentAmount(oldBill) : 0;
    const removeLinkedOrLegacy = tx => {
        // state.jointRegister is a single flat array spanning every month (unlike personalCalendar and
        // cardCalendars, which are already partitioned by month key) — without this guard, every call to
        // this function, though nominally scoped to one (year, month), would filter the ENTIRE jointRegister,
        // and since syncBillTrackerBillsToAllMonths() calls this once per month in a loop, each month's
        // pass would wipe out the ledger entries every other month's pass had just created for the same
        // bill, leaving only whichever month happened to be processed last.
        if (targetMonthPrefix && tx.date && !tx.date.startsWith(targetMonthPrefix)) return true;
        // "update the original charge on the calendar but only for the current day and all future charges"
        if (isRealCurrentMonth && tx.date < todayStr) {
            return true; // Do not touch past transactions in the current month
        }
        if (tx.linkedBillId === billId) {
            if (!force && oldBill) {
                const occurrenceDate = tx.billOccurrenceDate || tx.date;
                const label = tx.description || tx.name || tx.merchant || '';
                if (!expectedDates.includes(occurrenceDate) || Math.abs((Number(tx.amount) || 0) - expectedAmount) > 0.001 || label !== oldBill.account) tx.billOccurrenceOverridden = true;
            }
            if ((tx.billOccurrenceOverridden || tx.billOccurrenceDeleted) && !purgeOverrides) return true;
            return false;
        }
        if (!oldBill || tx.linkedBillId) return true;
        const label = tx.description || tx.name || tx.merchant;
        return !(expectedDates.includes(tx.date) && label === oldBill.account && Math.abs(Number(tx.amount) || 0) === Math.abs(expectedAmount));
    };
    if (state.personalCalendar[key]) state.personalCalendar[key] = state.personalCalendar[key].filter(removeLinkedOrLegacy);
    state.jointRegister = (state.jointRegister || []).filter(removeLinkedOrLegacy);
    Object.values(state.cardCalendars || {}).forEach(calendar => {
        if (calendar[key]) calendar[key] = calendar[key].filter(removeLinkedOrLegacy);
    });
}

function syncBillLedgerEntry(rawBill, year, month) {
    // Card-payment splitter rows are budget-only mirrors of a payment that already posted to the
    // checking ledger. Skipping entirely also keeps removeBillLedgerEntries' legacy matching from
    // ever deleting the real payment entry (same label, date, and amount, but no linkedBillId).
    if (rawBill.linkedCardPaymentId) return;
    const bill = recalculateBillBudgetForPeriod(rawBill, year, month);
    const forceClean = !!bill.isMortgage || !!bill.billTrackerSettingId;
    // purgeOverrides: false — this is a regeneration sync, so entries the user individually edited
    // or deleted must survive; their dates land in overriddenDates below and are skipped.
    removeBillLedgerEntries(bill.id, year, month, bill, forceClean, false);
    if (bill.entryType !== 'actual') return;
    const occurrenceAmount = getBillOccurrencePaymentAmount(bill);
    if (occurrenceAmount <= 0) return;
    const key = `${year}-${month}`;
    // Use the real calendar date here, not state.currentYear/currentMonth — that's just whichever
    // month the UI happens to be scrolled to, which has no relation to "today" and previously caused
    // an occurrence landing on the actual current date to be skipped whenever the app was parked on
    // a different month when the bill setting was saved.
    const todayStr = formatLocalDate(new Date());

    const overriddenDates = new Set(getBillLinkedLedgerEntries(bill.id).filter(tx => tx.billOccurrenceOverridden || tx.billOccurrenceDeleted).map(tx => tx.billOccurrenceDate || tx.date));
    getBillOccurrenceDates(bill, year, month).forEach(date => {
        // Do not generate calendar/register entries for dates strictly before today.
        if (date < todayStr) return;
        if (overriddenDates.has(date)) return;
        const common = { date, amount: -occurrenceAmount, linkedBillId: bill.id, linkedBillSeriesId: bill.recurringSeriesId || bill.id, billOccurrenceDate: date, splitterItem: true, owner: bill.ownership, isRecurring: !!bill.isRecurring, billOccurrenceOverridden: false, billOccurrenceDeleted: false };
        if (bill.paymentSource === 'personalChecking') {
            if (!state.personalCalendar[key]) state.personalCalendar[key] = [];
            state.personalCalendar[key].push({ id: 'p-' + Math.random().toString(36).substr(2, 9), description: bill.account, ...common });
        } else if (bill.paymentSource === 'jointChecking') {
            state.jointRegister.push({ id: 'j-' + Math.random().toString(36).substr(2, 9), type: 'expense', name: bill.account, ...common });
        } else {
            if (!state.cardCalendars) state.cardCalendars = {};
            if (!state.cardCalendars[bill.paymentSource]) state.cardCalendars[bill.paymentSource] = {};
            if (!state.cardCalendars[bill.paymentSource][key]) state.cardCalendars[bill.paymentSource][key] = [];
            state.cardCalendars[bill.paymentSource][key].push({ id: 'c-' + Math.random().toString(36).substr(2, 9), merchant: bill.account, description: bill.account, ...common });
        }
    });
}
function getBillLegacyRecurrenceKey(rawBill) {
    const bill = normalizeBillSplitterItem(rawBill);
    return `${bill.account.trim().toLowerCase()}|${bill.paymentSource}|${bill.entryType}|${bill.ownership}|${bill.category}`;
}
function deleteBillSplitterItem(bill, year, month, deleteFuture) {
    const seriesId = bill.recurringSeriesId || bill.id;
    const currentIndex = year * 12 + MONTH_ORDER.indexOf(month);
    if (!state.billRecurrenceSkips) state.billRecurrenceSkips = {};
    if (!state.billRecurrenceStops) state.billRecurrenceStops = {};
    if (!state.billRecurrenceTemplates) state.billRecurrenceTemplates = {};
    if (!state.billLegacyRecurrenceStops) state.billLegacyRecurrenceStops = {};
    if (bill.isRecurring) {
        if (deleteFuture) {
            state.billRecurrenceStops[seriesId] = currentIndex;
            delete state.billRecurrenceTemplates[seriesId];
        } else {
            state.billRecurrenceSkips[`${seriesId}|${year}-${month}`] = true;
            state.billRecurrenceTemplates[seriesId] = {
                bill: normalizeBillSplitterItem(bill),
                cycleKey: bill.cycleAllocation === '15th' ? 'cycle15th' : 'cycle1st',
                startIndex: currentIndex
            };
        }
    } else if (deleteFuture) {
        state.billLegacyRecurrenceStops[getBillLegacyRecurrenceKey(bill)] = currentIndex;
    }

    let removedCount = 0;
    Object.entries(state.monthlyBills || {}).forEach(([key, monthData]) => {
        const [keyYear, keyMonth] = key.split('-');
        const periodIndex = Number(keyYear) * 12 + MONTH_ORDER.indexOf(keyMonth);
        if (periodIndex < currentIndex || (!deleteFuture && key !== `${year}-${month}`)) return;
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            const list = monthData[cycleKey]?.bills || [];
            for (let index = list.length - 1; index >= 0; index--) {
                const candidate = normalizeBillSplitterItem(list[index], cycleKey);
                const candidateSeries = candidate.recurringSeriesId || candidate.id;
                const sameSeries = candidateSeries === seriesId;
                const sameLegacyBill = getBillLegacyRecurrenceKey(candidate) === getBillLegacyRecurrenceKey(bill);
                const shouldRemove = deleteFuture ? (sameSeries || sameLegacyBill) : candidate.id === bill.id;
                if (!shouldRemove) continue;
                const removed = list.splice(index, 1)[0];
                removeBillLedgerEntries(removed.id, Number(keyYear), keyMonth, removed, true);
                removedCount++;
            }
        });
        recalculateBillCycleTotals(monthData);
    });
    if (deleteFuture) {
        const isCurrentOrFuture = tx => {
            if (!tx?.date) return false;
            const parts = tx.date.split('-');
            return Number(parts[0]) * 12 + Number(parts[1]) - 1 >= currentIndex;
        };
        const matchesSeries = tx => tx.linkedBillSeriesId === seriesId || tx.linkedBillId === bill.id || String(tx.linkedBillId || '').startsWith(`${seriesId}-`);
        const matchesLegacy = tx => (tx.splitterItem || (bill.paymentSource === 'personalChecking' && tx.isRecurring)) &&
            (tx.description || tx.name || tx.merchant) === bill.account &&
            Math.abs(Math.abs(Number(tx.amount) || 0) - getBillOccurrencePaymentAmount(bill)) < 0.001;
        Object.keys(state.personalCalendar || {}).forEach(key => {
            state.personalCalendar[key] = (state.personalCalendar[key] || []).filter(tx => !(isCurrentOrFuture(tx) && (matchesSeries(tx) || (bill.paymentSource === 'personalChecking' && matchesLegacy(tx)))));
        });
        state.jointRegister = (state.jointRegister || []).filter(tx => !(isCurrentOrFuture(tx) && (matchesSeries(tx) || (bill.paymentSource === 'jointChecking' && matchesLegacy(tx)))));
        Object.entries(state.cardCalendars || {}).forEach(([cardId, calendar]) => {
            Object.keys(calendar || {}).forEach(key => {
                calendar[key] = (calendar[key] || []).filter(tx => !(isCurrentOrFuture(tx) && (matchesSeries(tx) || (bill.paymentSource === cardId && matchesLegacy(tx)))));
            });
        });
        reconcileCardCurrentBalances();
    }
    return removedCount;
}
function inheritRecurringBillsForMonth(year, month) {
    const targetKey = `${year}-${month}`;
    const targetIndex = year * 12 + MONTH_ORDER.indexOf(month);
    const latestBySeries = new Map();
    Object.entries(state.billRecurrenceTemplates || {}).forEach(([seriesId, template]) => {
        const endIndex = template.endIndex ?? getBillRecurrenceMonthIndex(template.bill?.recurringEndMonth);
        if (Number(template.startIndex) <= targetIndex && (endIndex === null || endIndex === undefined || targetIndex <= Number(endIndex))) latestBySeries.set(seriesId, { bill: template.bill, cycleKey: template.cycleKey || 'cycle1st', periodIndex: Number(template.startIndex) });
    });
    Object.keys(state.monthlyBills || {}).sort().forEach(key => {
        const [keyYear, keyMonth] = key.split('-');
        const periodIndex = Number(keyYear) * 12 + MONTH_ORDER.indexOf(keyMonth);
        if (periodIndex >= targetIndex) return;
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            (state.monthlyBills[key]?.[cycleKey]?.bills || []).forEach(raw => {
                const bill = normalizeBillSplitterItem(raw, cycleKey);
                // Bill Tracker settings already generate their own recurring occurrences via
                // syncBillTrackerBillsToAllMonths()/getBillOccurrenceDates (below), keyed by the stable
                // id `bill-settings-${settingId}`. Without this guard, this generic "carry the bill
                // forward" mechanism (meant for plain Bill Splitter rows manually marked recurring)
                // also clones them forward under a new `${id}-${year}-${month}` id, producing a second,
                // independently-tracked duplicate of every Bill Tracker charge from the second month on.
                if (bill.isRecurring && !bill.billTrackerSettingId) latestBySeries.set(bill.recurringSeriesId || bill.id, { bill, cycleKey, periodIndex });
            });
        });
    });
    const target = state.monthlyBills[targetKey];
    if (!target) return;
    const existingSeries = new Set(['cycle1st', 'cycle15th'].flatMap(cycleKey => (target[cycleKey].bills || []).map(bill => bill.recurringSeriesId).filter(Boolean)));
    latestBySeries.forEach(({ bill, cycleKey }) => {
        const seriesId = bill.recurringSeriesId || bill.id;
        const skipped = !!state.billRecurrenceSkips?.[`${seriesId}|${targetKey}`];
        const stoppedAt = state.billRecurrenceStops?.[seriesId];
        if (existingSeries.has(seriesId) || skipped || !isBillActiveForPeriod(bill, year, month) || (Number.isFinite(Number(stoppedAt)) && Number(stoppedAt) <= targetIndex)) return;
        target[cycleKey].bills.push(recalculateBillBudgetForPeriod({ ...bill, id: `${seriesId}-${year}-${month}`, recurringSeriesId: seriesId }, year, month, cycleKey));
        existingSeries.add(seriesId);
    });
}

// Derives Bill Splitter rows from scheduled credit card payments (both manual one-offs and
// strategy-generated automatic payments) so the transfer calculations budget for them. Rows are
// entryType 'calculation' — the payment itself already posted to the checking ledger, so these rows
// must never generate their own ledger entries (see the linkedCardPaymentId guard in
// syncBillLedgerEntry). Rows are re-derived from the payments on every sync; for automatic payments
// the user may customize the budget fields, which are then preserved via userBudgetCustomized.
function syncCardPaymentSplitterRowsForMonth(year, month) {
    const key = `${year}-${month}`;
    const mBills = state.monthlyBills[key];
    if (!mBills) return;
    const monthIndex = MONTH_ORDER.indexOf(month);
    if (monthIndex < 0) return;
    const prefix = `${year}-${String(monthIndex + 1).padStart(2, '0')}-`;

    const payments = [];
    (state.personalCalendar[key] || []).forEach(tx => {
        if (tx.payoffTargetId && !tx.billOccurrenceDeleted) payments.push({ tx, source: 'personal' });
    });
    (state.jointRegister || []).forEach(tx => {
        if (tx.payoffTargetId && tx.date && tx.date.startsWith(prefix) && !tx.billOccurrenceDeleted) payments.push({ tx, source: 'joint' });
    });

    const activeRowIds = new Set();
    payments.forEach(({ tx, source }) => {
        const card = state.loans.find(l => l.id === tx.payoffTargetId);
        if (!card) return;
        if (card.isExemptFromSplitter) return;
        const isAuto = !!tx.isAutomaticCardPayment;
        const linkKey = tx.automaticPaymentId || tx.linkedPaymentId || tx.id;
        const rowId = `card-pmt-${linkKey}`;
        activeRowIds.add(rowId);
        const day = Number(tx.date.slice(8, 10)) || 1;
        const dayCycle = day <= 14 ? '1st' : '15th';
        // Automatic payments recur monthly, so a user-chosen transfer cycle is saved on the card/loan
        // itself (splitterCycleOverride) and applied to every month's row here — current and future —
        // instead of the raw due-day default. Manual (one-time) payments keep their per-row override.
        const resolvedCycle = (isAuto && card.splitterCycleOverride) ? card.splitterCycleOverride : dayCycle;
        const targetCycleKey = resolvedCycle === '15th' ? 'cycle15th' : 'cycle1st';
        const amount = Math.abs(Number(tx.amount) || 0);

        let row = mBills.cycle1st.bills.find(b => b.id === rowId) || mBills.cycle15th.bills.find(b => b.id === rowId);
        if (!row) {
            row = {
                id: rowId,
                account: `Pmt: ${card.name}`,
                category: 'bill',
                entryType: 'calculation',
                ownership: source === 'joint' ? 'joint' : 'personal',
                paymentSource: source === 'joint' ? 'jointChecking' : 'personalChecking',
                dueDay: day,
                cycleAllocation: resolvedCycle,
                budgetAmount: amount,
                frequencyAmount: amount,
                paymentAmount: amount,
                occurrencePaymentAmount: amount,
                samePaymentAmount: true,
                amount: -amount,
                isRecurring: false,
                chargeFrequency: 'monthly',
                linkedCardPaymentId: linkKey,
                linkedPaymentDate: tx.date,
                cardPaymentKind: isAuto ? 'auto' : 'manual',
                payoffTargetId: card.id
            };
            mBills[targetCycleKey].bills.push(row);
        } else {
            row.account = `Pmt: ${card.name}`;
            row.dueDay = day;
            row.linkedPaymentDate = tx.date;
            row.ownership = source === 'joint' ? 'joint' : 'personal';
            row.paymentSource = source === 'joint' ? 'jointChecking' : 'personalChecking';
            row.cardPaymentKind = isAuto ? 'auto' : 'manual';
            row.payoffTargetId = card.id;
            row.paymentAmount = amount;
            row.occurrencePaymentAmount = amount;
            if (!(isAuto && row.userBudgetCustomized)) {
                row.budgetAmount = amount;
                row.frequencyAmount = amount;
                row.amount = -amount;
                row.samePaymentAmount = true;
            }
            if ((isAuto && card.splitterCycleOverride) || !row.userCycleCustomized) {
                row.cycleAllocation = resolvedCycle;
                row.userCycleCustomized = isAuto && !!card.splitterCycleOverride;
                const currentCycleKey = mBills.cycle1st.bills.includes(row) ? 'cycle1st' : 'cycle15th';
                if (currentCycleKey !== targetCycleKey) {
                    mBills[currentCycleKey].bills = mBills[currentCycleKey].bills.filter(b => b.id !== rowId);
                    mBills[targetCycleKey].bills.push(row);
                }
            }
        }
    });

    // Remove rows whose backing payment no longer exists in this month (deleted or moved).
    ['cycle1st', 'cycle15th'].forEach(cycleKey => {
        mBills[cycleKey].bills = mBills[cycleKey].bills.filter(b => !b.linkedCardPaymentId || activeRowIds.has(b.id));
    });
}

function autopopulateBillsForMonth(year, month) {
    const key = `${year}-${month}`;
    const mBills = state.monthlyBills[key];
    if (!mBills) return;
    inheritRecurringBillsForMonth(year, month);
    const targetIndex = year * 12 + MONTH_ORDER.indexOf(month);
    ['cycle1st', 'cycle15th'].forEach(cycleKey => {
        mBills[cycleKey].bills = (mBills[cycleKey].bills || []).filter(bill => {
            const stoppedAt = state.billLegacyRecurrenceStops?.[getBillLegacyRecurrenceKey(bill)];
            if (!Number.isFinite(Number(stoppedAt)) || Number(stoppedAt) > targetIndex) return true;
            removeBillLedgerEntries(bill.id, year, month, bill, true);
            return false;
        });
        mBills[cycleKey].bills = (mBills[cycleKey].bills || []).map(bill => recalculateBillBudgetForPeriod(bill, year, month, cycleKey));
        mBills[cycleKey].bills.forEach(bill => syncBillLedgerEntry(bill, year, month));
    });
    syncMortgageLoansToAllMonthsIfChanged();
    syncBillTrackerBillsToAllMonthsIfChanged();
    // Installment loans always auto-pay (no dashboard to visit to trigger it the way credit cards
    // do via renderCardDashboard), so generate their payment for this month directly here.
    state.loans.filter(l => l.type === 'loan' && !l.isMortgage).forEach(loan => {
        ensureAutomaticCardPaymentForMonth(loan.id, year, month);
    });
    syncCardPaymentSplitterRowsForMonth(year, month);
    recalculateBillCycleTotals(mBills);
}

function calculateCardLedgerBalance(cardId, throughDate = formatLocalDate(new Date())) {
    const card = state.loans.find(c => c.id === cardId);
    if (!card) return 0;

    let balance = Number(card.startBal) || 0;
    const cardCal = state.cardCalendars?.[cardId] || {};

    Object.values(cardCal).forEach(txs => {
        (txs || []).forEach(tx => {
            if (tx.billOccurrenceDeleted) return;
            const amount = Number(tx.amount);
            if (!Number.isFinite(amount) || !tx.date || tx.date > throughDate) return;
            balance += amount < 0 ? Math.abs(amount) : -Math.abs(amount);
        });
    });

    // Intentionally not clamped to 0: an overpayment should show up as a negative balance
    // (a credit owed back), not silently disappear. UI display code is responsible for
    // rendering a negative balance as a credit rather than treating it as an error.
    return balance;
}

let _cardBalanceEstimatesCache = {};

// Re-simulates a card's entire transaction history day-by-day (interest, promos,
// payment plans), so it's cached per card and only recomputed when saveDatabase()
// clears the cache — otherwise every keystroke in the list filters re-ran it.
function computeAllEstimatedBalancesForCard(cardId) {
    if (_cardBalanceEstimatesCache[cardId]) return _cardBalanceEstimatesCache[cardId];

    const card = state.loans.find(c => c.id === cardId);
    if (!card) return { estimates: {}, activePlans: [] };

    const cardCal = state.cardCalendars[cardId] || {};
    const allTxs = [];
    Object.keys(cardCal).forEach(key => {
        (cardCal[key] || []).forEach(tx => {
            if (tx.billOccurrenceDeleted) return;
            allTxs.push({ ...tx });
        });
    });

    if (allTxs.length === 0) return { estimates: {}, activePlans: [] };
    allTxs.sort((a, b) => new Date(a.date).getTime() - new Date(b.date).getTime());

    let estBalance = Number(card.startBal) || 0;
    const estimates = {};
    const activePlans = (card.paymentPlans || []).map(normalizePaymentPlan);

    const firstDate = new Date(allTxs[0].date + 'T00:00:00');
    const lastDate = new Date(allTxs[allTxs.length - 1].date + 'T00:00:00');
    const txsByDate = {};
    allTxs.forEach(tx => {
        if (!txsByDate[tx.date]) txsByDate[tx.date] = [];
        txsByDate[tx.date].push(tx);
    });

    const currentDate = new Date(firstDate);
    const statementDay = Number(card.statementDay) || 1;
    let lastInterestMonthYear = '';

    while (currentDate <= lastDate) {
        const dateStr = `${currentDate.getFullYear()}-${String(currentDate.getMonth() + 1).padStart(2, '0')}-${String(currentDate.getDate()).padStart(2, '0')}`;
        const dayOfMonth = currentDate.getDate();
        const currentMonthYear = `${currentDate.getFullYear()}-${currentDate.getMonth()}`;

        const dayTxs = txsByDate[dateStr] || [];
        dayTxs.forEach(tx => {
            const amount = Number(tx.amount) || 0;
            if (amount < 0) {
                estBalance += Math.abs(amount);
            } else {
                estBalance = Math.max(0, estBalance - amount);
            }
            estimates[tx.id] = estBalance;
        });

        if (dayOfMonth === statementDay && lastInterestMonthYear !== currentMonthYear) {
            lastInterestMonthYear = currentMonthYear;
            let activePlansFees = 0;
            let activePlansBalanceSum = 0;

            activePlans.forEach(plan => {
                const planStartDate = new Date(plan.startDate + 'T00:00:00');
                if (currentDate >= planStartDate) {
                    const monthsPassed = (currentDate.getFullYear() - planStartDate.getFullYear()) * 12 + currentDate.getMonth() - planStartDate.getMonth();
                    if (monthsPassed >= 0 && monthsPassed < plan.lengthMonths && plan.currentBalance > 0) {
                        activePlansFees += Number(plan.monthlyFee) || 0;
                        activePlansBalanceSum += Number(plan.currentBalance) || 0;
                        plan.currentBalance = Math.max(0, plan.currentBalance - plan.monthlyPayment);
                        if (plan.currentBalance <= 0) {
                            plan.isPaidOff = true;
                            plan.paidOffDateStr = dateStr;
                        }
                    }
                }
            });

            estBalance += activePlansFees;

            if (estBalance > 0.01) {
                let interestAccruingBalance = Math.max(0, estBalance - activePlansBalanceSum);
                let promoInterest = 0;
                let activePromosBalanceSum = 0;

                (card.promos || []).forEach(promo => {
                    if (promo.expDate) {
                        const expTime = new Date(promo.expDate + 'T00:00:00').getTime();
                        if (currentDate.getTime() <= expTime) {
                            const pBal = Number(promo.currentBalance ?? promo.amount) || 0;
                            promoInterest += pBal * (Number(promo.rate) / 12 / 100);
                            activePromosBalanceSum += pBal;
                        }
                    }
                });

                let purchaseRate = Number(card.interestRate) || 0;
                if (card.promoActive && card.promoExpDate) {
                    const promoExpTime = new Date(card.promoExpDate + 'T00:00:00').getTime();
                    if (currentDate.getTime() <= promoExpTime) {
                        purchaseRate = Number(card.promoRate) || 0;
                    }
                }

                const nonPromoBalance = Math.max(0, interestAccruingBalance - activePromosBalanceSum);
                const standardInterest = nonPromoBalance * (purchaseRate / 12 / 100);
                estBalance += (standardInterest + promoInterest);
            }

            dayTxs.forEach(tx => {
                estimates[tx.id] = estBalance;
            });
        }

        currentDate.setDate(currentDate.getDate() + 1);
    }

    const result = { estimates, activePlans };
    _cardBalanceEstimatesCache[cardId] = result;
    return result;
}

// syncMortgageLoansToAllMonths()/syncBillTrackerBillsToAllMonths() below are O(every month that
// exists) each — necessary when a mortgage loan or bill-tracker setting is actually added/edited, but
// autopopulateBillsForMonth() calls both on every single invocation, and it in turn gets called from
// getCalculatedTransferForJason()/getCalculatedTransferForAsia() on every cache miss. Materializing
// months far in the future (e.g. jumping straight to a month years out) triggers hundreds of those
// calls, each re-scanning every already-existing month — an O(months²) blowup that's the real cause of
// the multi-second freeze on a large jump. These "IfChanged" wrappers skip the expensive full re-sync
// unless the mortgage loans / bill-tracker settings actually changed since the last sync (compared via
// a cheap JSON signature), so the hot path only pays for it once until something real changes.
// Signature includes the month COUNT too, not just the settings — both sync functions iterate every
// key in state.monthlyBills, so a brand-new month (materialized mid-walk by ensureYearMonthInitialized)
// needs a fresh sync even when the settings themselves haven't changed, or that new month would never
// get its mortgage/bill-tracker-driven bills populated at all.
let _lastMortgageSyncSignature = null;
function syncMortgageLoansToAllMonthsIfChanged() {
    const mortgageLoans = state.loans.filter(l => l.type === 'loan' && l.isMortgage);
    const signature = JSON.stringify(mortgageLoans) + '|' + Object.keys(state.monthlyBills || {}).length;
    if (signature === _lastMortgageSyncSignature) return;
    _lastMortgageSyncSignature = signature;
    syncMortgageLoansToAllMonths();
}

let _lastBillTrackerSyncSignature = null;
function syncBillTrackerBillsToAllMonthsIfChanged() {
    const signature = JSON.stringify(state.billTrackerSettings || []) + '|' + Object.keys(state.monthlyBills || {}).length;
    if (signature === _lastBillTrackerSyncSignature) return;
    _lastBillTrackerSyncSignature = signature;
    syncBillTrackerBillsToAllMonths();
}

function syncMortgageLoansToAllMonths() {
    const mortgageLoans = state.loans.filter(l => l.type === 'loan' && l.isMortgage);

    Object.keys(state.monthlyBills || {}).forEach(key => {
        const mBills = state.monthlyBills[key];
        if (!mBills) return;
        
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            mBills[cycleKey].bills = (mBills[cycleKey].bills || []).filter(b => {
                if (b.isMortgage) {
                    return mortgageLoans.some(l => `mortgage-bill-${l.id}` === b.id);
                }
                // Filter out legacy duplicate template bills matching the loan name or containing "mortgage"
                const isLegacyMortgage = mortgageLoans.some(l => 
                    b.account === `Mortgage: ${l.name}` || 
                    b.account === l.name ||
                    (l.name.toLowerCase().includes('mortgage') && b.account.toLowerCase().includes('mortgage'))
                );
                if (isLegacyMortgage) {
                    const [y, m] = key.split('-');
                    removeBillLedgerEntries(b.id, Number(y), m, b, true);
                    return false;
                }
                return true;
            });
        });
        
        mortgageLoans.forEach(loan => {
            const billId = `mortgage-bill-${loan.id}`;
            // Transfer cycle: respect an explicit user override (splitterCycleOverride, shared with
            // the card/loan payment sync) instead of always deriving it from the due day, so mortgage
            // payments can be split/reassigned like any other dynamic Bill Splitter entry. Note
            // cycleAllocation must be '1st'/'15th'/'both' (the convention every other bill type uses),
            // not the storage-array key 'cycle1st'/'cycle15th' this used to be set to by mistake.
            const dayCycle = loan.dueDay <= 14 ? '1st' : '15th';
            const resolvedCycle = loan.splitterCycleOverride || dayCycle;
            const cycleKey = resolvedCycle === '15th' ? 'cycle15th' : 'cycle1st';

            let bill = mBills.cycle1st.bills.find(b => b.id === billId) || mBills.cycle15th.bills.find(b => b.id === billId);
            const actualPayment = (Number(loan.escrowAmount) || 0) + (Number(loan.piAmount) || 0);
            const minPayment = actualPayment + (Number(loan.extraPayment) || 0);
            const budgetAmount = Number(loan.monthlyMin) || actualPayment;
            
            if (bill) {
                bill.account = `Mortgage: ${loan.name}`;
                bill.dueDay = Number(loan.dueDay) || 15;
                bill.cycleAllocation = resolvedCycle;
                
                // Initialize manual properties if not set
                if (bill.manualTransferAmount === undefined || bill.manualTransferAmount === null) {
                    bill.manualTransferAmount = bill.budgetAmount !== undefined ? bill.budgetAmount : budgetAmount;
                }
                if (bill.manualSamePaymentAmount === undefined || bill.manualSamePaymentAmount === null) {
                    bill.manualSamePaymentAmount = bill.samePaymentAmount !== undefined ? bill.samePaymentAmount : true;
                }
                if (bill.manualOccurrencePaymentAmount === undefined || bill.manualOccurrencePaymentAmount === null) {
                    bill.manualOccurrencePaymentAmount = bill.occurrencePaymentAmount !== undefined ? bill.occurrencePaymentAmount : actualPayment;
                }
                
                const wasOverridden = !!bill.isMortgageOverrideActive;
                
                if (minPayment > bill.manualTransferAmount) {
                    bill.budgetAmount = minPayment;
                    bill.amount = -Math.abs(minPayment);
                    bill.frequencyAmount = minPayment;
                    bill.samePaymentAmount = true;
                    bill.paymentAmount = minPayment;
                    bill.occurrencePaymentAmount = minPayment;
                    bill.isMortgageOverrideActive = true;
                } else {
                    bill.budgetAmount = bill.manualTransferAmount;
                    bill.amount = -Math.abs(bill.manualTransferAmount);
                    bill.frequencyAmount = bill.manualTransferAmount;
                    if (wasOverridden) {
                        bill.samePaymentAmount = false;
                        bill.manualSamePaymentAmount = false;
                    } else {
                        bill.samePaymentAmount = bill.manualSamePaymentAmount ?? false;
                    }
                    bill.occurrencePaymentAmount = actualPayment;
                    bill.paymentAmount = bill.samePaymentAmount ? bill.budgetAmount : actualPayment;
                    bill.isMortgageOverrideActive = false;
                }
                
                const currentCycle = mBills.cycle1st.bills.includes(bill) ? 'cycle1st' : 'cycle15th';
                if (currentCycle !== cycleKey) {
                    mBills[currentCycle].bills = mBills[currentCycle].bills.filter(b => b.id !== billId);
                    mBills[cycleKey].bills.push(bill);
                }
            } else {
                mBills[cycleKey].bills.push({
                    id: billId,
                    account: `Mortgage: ${loan.name}`,
                    category: 'bill',
                    amount: -Math.abs(budgetAmount),
                    budgetAmount: budgetAmount,
                    frequencyAmount: budgetAmount,
                    paymentAmount: actualPayment,
                    occurrencePaymentAmount: actualPayment,
                    dueDay: Number(loan.dueDay) || 15,
                    paymentSource: 'jointChecking',
                    ownership: 'joint',
                    cycleAllocation: resolvedCycle,
                    isRecurring: true,
                    isMortgage: true,
                    mortgageLoanId: loan.id,
                    manualTransferAmount: budgetAmount,
                    manualSamePaymentAmount: true,
                    manualOccurrencePaymentAmount: actualPayment
                });
            }
        });
        
        recalculateBillCycleTotals(mBills);
    });
}

// Returns the purchase APR that applies at a given point in the future, accounting for an active
// promo rate (card.promoActive/promoRate/promoExpDate) that expires partway through a payoff plan.
// monthsFromNow=0 is the current month.
function getEffectiveCardRateForMonth(card, monthsFromNow) {
    if (card.promoActive && card.promoExpDate) {
        const target = new Date();
        target.setDate(1);
        target.setMonth(target.getMonth() + monthsFromNow);
        if (target.getTime() <= new Date(card.promoExpDate + 'T00:00:00').getTime()) {
            return Number(card.promoRate) || 0;
        }
    }
    return Number(card.interestRate) || 0;
}

// Simulates a fixed monthly payment against a balance, applying each month's effective APR
// (which may change when a promo rate expires), and returns the number of months to reach $0.
// Returns Infinity if the payment never overtakes accruing interest within the cap.
function simulatePayoffMonthsWithPayment(balance, card, payment, capMonths = 600) {
    if (balance <= 0) return 0;
    if (payment <= 0) return Infinity;
    let remaining = balance;
    for (let m = 0; m < capMonths; m++) {
        const monthlyRate = Math.max(0, getEffectiveCardRateForMonth(card, m)) / 1200;
        remaining += remaining * monthlyRate;
        remaining -= payment;
        if (remaining <= 0) return m + 1;
    }
    return Infinity;
}

// Suggests the monthly payment needed to pay off `balance` in exactly `months`, accounting for
// a promo rate that may expire partway through the plan. Binary-searches on payment amount since
// a closed-form formula only exists for a constant rate across the whole period.
function calculateMonthlyPayoff(balance, card, months) {
    if (balance <= 0 || months <= 0) return 0;
    let lo = balance / months;
    let hi = balance / months + balance; // guaranteed to clear even a very high APR within `months`
    for (let i = 0; i < 60; i++) {
        const mid = (lo + hi) / 2;
        const monthsNeeded = simulatePayoffMonthsWithPayment(balance, card, mid, months + 1);
        if (monthsNeeded <= months) hi = mid; else lo = mid;
    }
    return hi;
}

function monthsUntilDate(targetDate) {
    const today = new Date();
    const target = new Date(targetDate + 'T00:00:00');
    return Math.max(0, (target.getFullYear() - today.getFullYear()) * 12 + target.getMonth() - today.getMonth());
}

function estimatePayoffMonths(balance, card, payment) {
    return simulatePayoffMonthsWithPayment(balance, card, payment);
}

function reconcileCardCurrentBalances() {
    let changed = false;

    state.loans.forEach(card => {
        if (card.type !== 'credit') return;
        const ledgerBalance = calculateCardLedgerBalance(card.id);
        if (Math.abs((Number(card.currentBal) || 0) - ledgerBalance) > 0.001) {
            card.currentBal = ledgerBalance;
            changed = true;
        }
    });

    if (changed) saveDatabase();
}

function getCardRunningBalanceAtDate(cardId, targetDateStr) {
    const card = state.loans.find(c => c.id === cardId);
    if (!card) return 0;
    
    let balance = card.startBal || 0;
    const targetTime = new Date(targetDateStr + 'T00:00:00').getTime();
    
    const cardCal = state.cardCalendars[cardId] || {};
    const sortedKeys = Object.keys(cardCal).sort((a, b) => {
        const [yA, mA] = a.split('-');
        const [yB, mB] = b.split('-');
        if (parseInt(yA) !== parseInt(yB)) return parseInt(yA) - parseInt(yB);
        return MONTH_ORDER.indexOf(mA) - MONTH_ORDER.indexOf(mB);
    });
    
    sortedKeys.forEach(key => {
        const txs = cardCal[key] || [];
        txs.forEach(tx => {
            if (new Date(tx.date + 'T00:00:00').getTime() < targetTime) {
                // Expenses (negative amount) increase balance owed.
                // Payments (positive amount) decrease balance owed.
                if (tx.amount < 0) {
                    balance += Math.abs(tx.amount);
                } else {
                    balance -= tx.amount;
                }
            }
        });
    });
    
    return balance;
}

// --- CREDIT CARD SUB-DASHBOARD & DETAILS EDITING ---
let tempEditingPromos = [];
let tempEditingPaymentPlans = [];
let editingPaymentPlanId = '';

function resetExistingPlanEditor() {
    ['existing-plan-name','existing-plan-original','existing-plan-current','existing-plan-length','existing-plan-remaining-payments','existing-plan-payment'].forEach(id => document.getElementById(id).value = '');
    document.getElementById('existing-plan-fee').value = '0';
    document.getElementById('existing-plan-activated').value = formatLocalDate(new Date());
    editingPaymentPlanId = '';
    document.getElementById('btn-add-existing-plan').textContent = 'Add Existing Plan';
    document.getElementById('btn-cancel-plan-edit').classList.add('hidden');
}

function calculatePlanPayoffDate(plan) {
    const payment = Number(plan.monthlyPayment) || 0;
    const balance = Number(plan.currentBalance) || 0;
    if (payment <= 0 || balance <= 0) return '';
    const months = Number.isFinite(Number(plan.remainingPayments)) ? Math.max(0, Number(plan.remainingPayments)) : Math.ceil(balance / payment);
    const date = new Date();
    date.setMonth(date.getMonth() + months);
    return formatLocalDate(date);
}

function normalizePaymentPlan(plan) {
    const normalized = {
        id: plan.id || 'plan-' + Math.random().toString(36).substr(2, 9),
        name: plan.name || 'Payment Plan',
        sourceTransactionId: plan.sourceTransactionId || '',
        originalAmount: Math.max(0, Number(plan.originalAmount) || 0),
        currentBalance: Math.max(0, Number(plan.currentBalance) || 0),
        lengthMonths: Math.max(1, Number(plan.lengthMonths) || 1),
        monthlyPayment: Math.max(0, Number(plan.monthlyPayment) || 0),
        monthlyFee: Math.max(0, Number(plan.monthlyFee) || 0),
        remainingPayments: Math.max(0, Number.isFinite(Number(plan.remainingPayments)) ? Number(plan.remainingPayments) : Math.ceil((Number(plan.currentBalance) || 0) / (Number(plan.monthlyPayment) || 1))),
        startDate: plan.startDate || formatLocalDate(new Date())
    };
    normalized.payoffDate = calculatePlanPayoffDate(normalized);
    return normalized;
}

function calculateInterestSavingPayment(card, throughDate = formatLocalDate(new Date())) {
    const plans = (card.paymentPlans || []).map(normalizePaymentPlan).filter(plan => plan.currentBalance > 0);
    const planBalances = plans.reduce((sum, plan) => sum + plan.currentBalance, 0);
    const nonPlanBalance = Math.max(0, calculateCardLedgerBalance(card.id, throughDate) - planBalances);
    const planDue = plans.reduce((sum, plan) => sum + plan.monthlyPayment + plan.monthlyFee, 0);
    return nonPlanBalance + planDue;
}

function renderEditingPaymentPlans() {
    const list = document.getElementById('loan-payment-plans-list');
    list.replaceChildren();
    tempEditingPaymentPlans.forEach(plan => {
        const item = document.createElement('div');
        item.className = 'payment-plan-row';
        item.innerHTML = `<span><strong>${escapeHTML(plan.name)}</strong> — Activated ${plan.startDate || '—'} • ${plan.remainingPayments} payments remaining • $${plan.currentBalance.toFixed(2)} balance • $${plan.monthlyPayment.toFixed(2)} + $${plan.monthlyFee.toFixed(2)} fee/month • Payoff ${plan.payoffDate || 'TBD'}</span><div style="display:flex; gap:.4rem;"><button type="button" class="action-btn small-btn edit-plan-btn">Edit</button><button type="button" class="action-btn small-btn danger-btn delete-plan-btn">Delete</button></div>`;
        item.querySelector('.edit-plan-btn').addEventListener('click', () => {
            editingPaymentPlanId = plan.id;
            document.getElementById('existing-plan-name').value = plan.name;
            document.getElementById('existing-plan-original').value = plan.originalAmount;
            document.getElementById('existing-plan-current').value = plan.currentBalance;
            document.getElementById('existing-plan-activated').value = plan.startDate || '';
            document.getElementById('existing-plan-length').value = plan.lengthMonths;
            document.getElementById('existing-plan-remaining-payments').value = plan.remainingPayments;
            document.getElementById('existing-plan-payment').value = plan.monthlyPayment;
            document.getElementById('existing-plan-fee').value = plan.monthlyFee;
            document.getElementById('btn-add-existing-plan').textContent = 'Update Plan';
            document.getElementById('btn-cancel-plan-edit').classList.remove('hidden');
            document.getElementById('existing-plan-name').focus();
        });
        item.querySelector('.delete-plan-btn').addEventListener('click', () => {
            tempEditingPaymentPlans = tempEditingPaymentPlans.filter(item => item.id !== plan.id);
            if (editingPaymentPlanId === plan.id) resetExistingPlanEditor();
            renderEditingPaymentPlans();
        });
        list.appendChild(item);
    });
    if (!tempEditingPaymentPlans.length) list.innerHTML = '<span class="muted-text">No payment plans recorded.</span>';
}
function populateTransactionPaymentPlanFields(tx, cardId) {
    const plan = (state.loans.find(card => card.id === cardId)?.paymentPlans || []).find(item => item.sourceTransactionId === tx.id);
    const checkbox = document.getElementById('edit-tx-payment-plan');
    checkbox.checked = !!plan;
    document.getElementById('edit-payment-plan-fields').classList.toggle('hidden', !plan);
    document.getElementById('edit-plan-activated').value = plan?.startDate || tx.date || formatLocalDate(new Date());
    document.getElementById('edit-plan-length').value = plan?.lengthMonths || '';
    document.getElementById('edit-plan-current').value = plan?.currentBalance ?? Math.abs(tx.amount);
    document.getElementById('edit-plan-payment').value = plan?.monthlyPayment || '';
    document.getElementById('edit-plan-fee').value = plan?.monthlyFee || 0;
}

function updateTransactionPaymentPlan(cardId, tx, enabled) {
    const card = state.loans.find(item => item.id === cardId);
    if (!card) return;
    if (!card.paymentPlans) card.paymentPlans = [];
    const existingIndex = card.paymentPlans.findIndex(plan => plan.sourceTransactionId === tx.id);
    if (!enabled) {
        if (existingIndex > -1) card.paymentPlans.splice(existingIndex, 1);
        delete tx.paymentPlanId;
        return;
    }

    const plan = normalizePaymentPlan({
        id: existingIndex > -1 ? card.paymentPlans[existingIndex].id : `plan-${tx.id}`,
        name: tx.merchant || tx.description || 'Transaction Plan',
        sourceTransactionId: tx.id,
        originalAmount: existingIndex > -1 ? card.paymentPlans[existingIndex].originalAmount : Math.abs(tx.amount),
        currentBalance: parseFloat(document.getElementById('edit-plan-current').value) || Math.abs(tx.amount),
        lengthMonths: parseInt(document.getElementById('edit-plan-length').value) || 1,
        monthlyPayment: parseFloat(document.getElementById('edit-plan-payment').value) || 0,
        monthlyFee: parseFloat(document.getElementById('edit-plan-fee').value) || 0,
        remainingPayments: existingIndex > -1 ? card.paymentPlans[existingIndex].remainingPayments : undefined,
        startDate: document.getElementById('edit-plan-activated').value || tx.date
    });
    if (existingIndex > -1) card.paymentPlans[existingIndex] = plan;
    else card.paymentPlans.push(plan);
    tx.paymentPlanId = plan.id;
}
function cleanupDuplicateBillSplitterCardCharges(cardId) {
    const cardCalendar = state.cardCalendars?.[cardId];
    if (!cardCalendar) return 0;
    let removed = 0;
    Object.entries(cardCalendar).forEach(([key, list]) => {
        const expectedBills = ['cycle1st', 'cycle15th'].flatMap(cycleKey => state.monthlyBills?.[key]?.[cycleKey]?.bills || []);
        const groups = new Map();
        (list || []).forEach(tx => {
            if (!tx.splitterItem || !tx.linkedBillSeriesId) return;
            const groupKey = `${tx.linkedBillSeriesId}|${tx.date}`;
            if (!groups.has(groupKey)) groups.set(groupKey, []);
            groups.get(groupKey).push(tx);
        });
        groups.forEach(group => {
            if (group.length < 2) return;
            const expectedBill = expectedBills.find(bill => (bill.recurringSeriesId || bill.id) === group[0].linkedBillSeriesId && bill.paymentSource === cardId);
            const overridden = group.find(tx => tx.billOccurrenceOverridden);
            const keep = overridden
                || group.find(tx => expectedBill && tx.linkedBillId === expectedBill.id)
                || group[0];
            if (overridden && expectedBill) {
                keep.linkedBillId = expectedBill.id;
                keep.linkedBillSeriesId = expectedBill.recurringSeriesId || expectedBill.id;
            }
            const duplicateIds = new Set(group.filter(tx => tx !== keep).map(tx => tx.id));
            cardCalendar[key] = cardCalendar[key].filter(tx => !duplicateIds.has(tx.id));
            removed += duplicateIds.size;
        });
    });
    if (state.recurringChargeTemplates?.[cardId]) {
        Object.keys(state.recurringChargeTemplates[cardId]).forEach(seriesId => {
            if (state.recurringChargeTemplates[cardId][seriesId]?.splitterItem) delete state.recurringChargeTemplates[cardId][seriesId];
        });
    }
    return removed;
}

function ensureRecurringCardChargesForMonth(cardId, year, month) {
    const cardCal = state.cardCalendars?.[cardId];
    if (!cardCal) return;
    cleanupDuplicateBillSplitterCardCharges(cardId);
    const targetIndex = year * 12 + MONTH_ORDER.indexOf(month);
    const seriesRoots = new Map();
    let changed = false;

    Object.values(state.recurringChargeTemplates?.[cardId] || {}).forEach(template => {
        if (template?.isRecurring && !template.splitterItem && template.amount < 0 && template.recurringSeriesId) seriesRoots.set(template.recurringSeriesId, template);
    });

    Object.values(cardCal).flatMap(list => list || []).forEach(tx => {
        if (tx.splitterItem || !tx.isRecurring || tx.amount >= 0) return;
        if (!tx.recurringSeriesId) {
            tx.recurringSeriesId = `series-${tx.id || Math.random().toString(36).substr(2, 9)}`;
            changed = true;
        }
        const existing = seriesRoots.get(tx.recurringSeriesId);
        if (!existing || tx.date < existing.date) seriesRoots.set(tx.recurringSeriesId, tx);
    });

    const key = `${year}-${month}`;
    if (!cardCal[key]) cardCal[key] = [];
    seriesRoots.forEach(root => {
        const seriesEndDate = state.recurringSeriesEndDates?.[root.recurringSeriesId];
        const targetMonthStart = `${year}-${String(MONTH_ORDER.indexOf(month) + 1).padStart(2, '0')}-01`;
        if (seriesEndDate && targetMonthStart >= seriesEndDate.slice(0, 8) + '01') return;
        const rootDate = new Date(root.date + 'T00:00:00');
        const rootIndex = rootDate.getFullYear() * 12 + rootDate.getMonth();
        if (targetIndex <= rootIndex) return;
        if (cardCal[key].some(tx => tx.recurringSeriesId === root.recurringSeriesId)) return;

        const monthIndex = MONTH_ORDER.indexOf(month);
        const effectiveDate = root.recurringTemplateEffectiveDate
            ? new Date(root.recurringTemplateEffectiveDate + 'T00:00:00')
            : null;
        const effectiveIndex = effectiveDate ? effectiveDate.getFullYear() * 12 + effectiveDate.getMonth() : Infinity;
        const template = root.recurringTemplate && targetIndex >= effectiveIndex ? root.recurringTemplate : root;
        const daysInMonth = new Date(year, monthIndex + 1, 0).getDate();
        const day = Math.min(Number(template.recurringDay) || rootDate.getDate(), daysInMonth);
        cardCal[key].push({
            ...root,
            ...template,
            id: 'c-' + Math.random().toString(36).substr(2, 9),
            date: `${year}-${String(monthIndex + 1).padStart(2, '0')}-${String(day).padStart(2, '0')}`,
            isRecurringOccurrence: true
        });
        changed = true;
    });
    if (changed) saveDatabase();
}

function propagateRecurringChargeChanges(cardId, editedTx) {
    if (editedTx.splitterItem || !editedTx.isRecurring || editedTx.amount >= 0) return;
    if (!editedTx.recurringSeriesId) {
        editedTx.recurringSeriesId = `series-${editedTx.id || Math.random().toString(36).substr(2, 9)}`;
    }

    if (!state.recurringChargeTemplates[cardId]) state.recurringChargeTemplates[cardId] = {};
    state.recurringChargeTemplates[cardId][editedTx.recurringSeriesId] = { ...editedTx };

    const series = Object.values(state.cardCalendars?.[cardId] || {})
        .flatMap(list => list || [])
        .filter(tx => tx.recurringSeriesId === editedTx.recurringSeriesId);
    if (series.length === 0) return;

    const template = {
        merchant: editedTx.merchant || '',
        description: editedTx.description,
        amount: editedTx.amount,
        owner: editedTx.owner || 'personal',
        trip: editedTx.trip || '',
        interestRate: editedTx.interestRate,
        isRecurring: true,
        recurringDay: editedTx.recurringDay || new Date(editedTx.date + 'T00:00:00').getDate(),
        recurringSeriesId: editedTx.recurringSeriesId
    };

    const root = series.reduce((earliest, tx) => tx.date < earliest.date ? tx : earliest, series[0]);
    root.recurringTemplate = { ...template };
    root.recurringTemplateEffectiveDate = editedTx.date;

    series.forEach(tx => {
        if (tx === editedTx || tx.date <= editedTx.date) return;
        Object.assign(tx, template);
        const dateObj = new Date(tx.date + 'T00:00:00');
        const daysInMonth = new Date(dateObj.getFullYear(), dateObj.getMonth() + 1, 0).getDate();
        const day = Math.min(template.recurringDay, daysInMonth);
        tx.date = `${dateObj.getFullYear()}-${String(dateObj.getMonth() + 1).padStart(2, '0')}-${String(day).padStart(2, '0')}`;
    });
}
function deleteCardTransactionWithRecurringChoice(cardId, key, id) {
    const list = state.cardCalendars?.[cardId]?.[key] || [];
    const tx = list.find(item => item.id === id);
    if (!tx) return null;

    if (tx.isAutomaticCardPayment) {
        alert('Automatic card payments cannot be deleted. To stop them, change the card’s payment strategy (Credit Cards → Edit Card). To pay a different amount this month, edit the payment instead.');
        return null;
    }

    if (tx.splitterItem) {
        tx.billOccurrenceDeleted = true;
        return tx;
    }

    const card = state.loans.find(item => item.id === cardId);
    if (card?.paymentPlans) card.paymentPlans = card.paymentPlans.filter(plan => plan.sourceTransactionId !== tx.id);

    if (tx.isRecurring && tx.recurringSeriesId) {
        const deleteRemaining = confirm('This is a recurring charge.\n\nOK: Delete this charge and all remaining charges in the series.\nCancel: Delete only this occurrence.');
        if (deleteRemaining) {
            if (!state.recurringSeriesEndDates) state.recurringSeriesEndDates = {};
            state.recurringSeriesEndDates[tx.recurringSeriesId] = tx.date;
            if (state.recurringChargeTemplates?.[cardId]) delete state.recurringChargeTemplates[cardId][tx.recurringSeriesId];
            Object.values(state.cardCalendars[cardId]).forEach(monthList => {
                for (let i = monthList.length - 1; i >= 0; i--) {
                    const item = monthList[i];
                    if (item.recurringSeriesId === tx.recurringSeriesId && item.date >= tx.date) monthList.splice(i, 1);
                }
            });
            return tx;
        }
    }

    list.splice(list.indexOf(tx), 1);
    removeLinkedCheckingPaymentLeg(tx);
    return tx;
}
function setupInlineAutocomplete(inputId, datalistId) {
    const input = document.getElementById(inputId);
    const datalist = document.getElementById(datalistId);

    input.addEventListener('input', (event) => {
        if (event.inputType?.startsWith('delete')) return;
        const typed = input.value;
        if (!typed || input.selectionStart !== typed.length) return;

        const match = Array.from(datalist.options)
            .map(option => option.value)
            .find(value => value.length > typed.length && value.toLocaleLowerCase().startsWith(typed.toLocaleLowerCase()));
        if (!match) return;

        input.value = match;
        input.setSelectionRange(typed.length, match.length);
    });

    input.addEventListener('keydown', (event) => {
        if (event.key === 'Tab' && input.selectionStart !== input.selectionEnd) {
            input.setSelectionRange(input.value.length, input.value.length);
        }
    });
}
function setupCCDashboardListeners() {
    setupInlineAutocomplete('cc-trans-merchant', 'cc-merchant-suggestions');
    setupInlineAutocomplete('cc-trans-desc', 'cc-description-suggestions');
    setupInlineAutocomplete('cc-list-add-merchant', 'cc-merchant-suggestions');
    setupInlineAutocomplete('cc-list-add-desc', 'cc-description-suggestions');

    // Back button
    document.getElementById('btn-cc-back').addEventListener('click', () => {
        state.ccSelectedCardId = '';
        renderCreditCardsTab();
    });
    
    // View mode toggle
    document.querySelectorAll('#cc-view-toggle .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            state.ccViewMode = e.target.dataset.mode;
            document.querySelectorAll('#cc-view-toggle .segment-btn').forEach(b => b.classList.toggle('active', b === e.target));
            
            document.getElementById('cc-calendar-view-container').classList.toggle('hidden', state.ccViewMode === 'list');
            document.getElementById('cc-list-view-container').classList.toggle('hidden', state.ccViewMode === 'calendar');
            document.getElementById('cc-scope-toggle').classList.toggle('hidden', state.ccViewMode === 'calendar');
            
            renderCardDashboard(state.ccSelectedCardId);
        });
    });
    
    // List scope toggle
    document.querySelectorAll('#cc-scope-toggle .segment-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            state.ccListScope = e.target.dataset.scope;
            document.querySelectorAll('#cc-scope-toggle .segment-btn').forEach(b => b.classList.toggle('active', b === e.target));
            renderCardDashboard(state.ccSelectedCardId);
        });
    });
    
    // (Local card period selectors and pickers removed, handled by header period selector)
    
    // Quick-Add Charge form submit
    document.getElementById('cc-quick-add-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const dateStr = document.getElementById('cc-trans-date').value;
        const merchant = document.getElementById('cc-trans-merchant').value.trim();
        const desc = document.getElementById('cc-trans-desc').value;
        const amount = parseFloat(document.getElementById('cc-trans-amount').value);
        const kind = document.getElementById('cc-trans-kind').value;
        const owner = document.getElementById('cc-trans-owner').value;
        const trip = document.getElementById('cc-trans-trip').value.trim();
        const isRecurring = document.getElementById('cc-trans-recurring').checked;
        const recurringDay = parseInt(document.getElementById('cc-trans-recurring-day').value) || 0;
        
        if (!dateStr || !desc || isNaN(amount) || amount <= 0) return;
        
        const cardId = state.ccSelectedCardId;
        const dateObj = new Date(dateStr + 'T00:00:00');
        const y = dateObj.getFullYear();
        const mShort = MONTH_ORDER[dateObj.getMonth()];
        const key = `${y}-${mShort}`;
        
        if (!state.cardCalendars) state.cardCalendars = {};
        if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
        if (!state.cardCalendars[cardId][key]) state.cardCalendars[cardId][key] = [];
        
        const activeCard = state.loans.find(l => l.id === cardId);
        
        // --- PAYMENT KIND: create linked checking + card entries ---
        if (kind === 'payment') {
            const source = owner;
            const linkId = 'manual-pmt-' + Math.random().toString(36).substr(2, 9);
            ensureYearMonthInitialized(y, mShort);
            
            const checkingTxId = (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9);
            const pmtDesc = `Pmt: ${activeCard ? activeCard.name : 'Card'}`;
            
            if (source === 'personal') {
                state.personalCalendar[key].push({
                    id: checkingTxId, date: dateStr, description: pmtDesc,
                    amount: -Math.abs(amount), linkedPaymentId: linkId, payoffTargetId: cardId
                });
            } else {
                state.jointRegister.push({
                    id: checkingTxId, date: dateStr, name: pmtDesc, description: pmtDesc,
                    amount: -Math.abs(amount), linkedPaymentId: linkId, payoffTargetId: cardId
                });
            }
            
            state.cardCalendars[cardId][key].push({
                id: 'c-' + Math.random().toString(36).substr(2, 9),
                date: dateStr,
                description: `Payment from ${source === 'joint' ? 'Joint' : 'Personal'} Checking`,
                amount: Math.abs(amount), transactionKind: 'payment', owner: source,
                linkedPaymentId: linkId, payoffTargetId: cardId
            });
            
            if (activeCard) activeCard.currentBal = Math.max(0, activeCard.currentBal - amount);
            
            saveDatabase();
            renderCardDashboard(cardId);
            document.getElementById('cc-trans-merchant').value = '';
            document.getElementById('cc-trans-desc').value = '';
            document.getElementById('cc-trans-amount').value = '';
            document.getElementById('cc-trans-kind').value = 'charge';
            document.getElementById('cc-trans-owner').value = 'personal';
            document.getElementById('cc-trans-trip').value = '';
            document.getElementById('cc-trans-recurring').checked = false;
            document.getElementById('cc-recurring-day-group').classList.add('hidden');
            document.getElementById('cc-trans-recurring-day').value = '';
            logSuccess(`Payment of $${amount.toFixed(2)} to ${activeCard ? activeCard.name : 'Card'} recorded from ${source === 'joint' ? 'Joint' : 'Personal'} Checking.`);
            return;
        }
        
        // --- CHARGE / CREDIT KIND ---
        const signedAmount = kind === 'credit' ? Math.abs(amount) : -Math.abs(amount);
        let txRate = activeCard ? (activeCard.interestRate || 0) : 0;
        if (activeCard && activeCard.promoActive && activeCard.promoExpDate) {
            const txTime = new Date(dateStr + 'T00:00:00').getTime();
            const expTime = new Date(activeCard.promoExpDate + 'T00:00:00').getTime();
            if (txTime <= expTime) {
                txRate = activeCard.promoRate || 0;
            }
        }

        const recurringEnabled = kind === 'charge' && isRecurring;
        const recurringSeriesId = recurringEnabled ? 'series-' + Math.random().toString(36).substr(2, 9) : '';
        const newTransaction = {
            id: 'c-' + Math.random().toString(36).substr(2, 9),
            date: dateStr, merchant, description: desc, amount: signedAmount,
            transactionKind: kind, owner, trip, interestRate: txRate,
            isRecurring: recurringEnabled,
            recurringDay: recurringEnabled ? (recurringDay || dateObj.getDate()) : 0,
            recurringSeriesId
        };
        const today = new Date();
        today.setHours(0, 0, 0, 0);
        const shouldPostNow = !recurringEnabled || dateObj > today;
        if (recurringEnabled) {
            if (!state.recurringChargeTemplates[cardId]) state.recurringChargeTemplates[cardId] = {};
            state.recurringChargeTemplates[cardId][recurringSeriesId] = { ...newTransaction };
        }
        if (shouldPostNow) {
            state.cardCalendars[cardId][key].push(newTransaction);
            adjustCardCurrentBalance(cardId, signedAmount);
        }
        
        saveDatabase();
        renderCardDashboard(cardId);
        
        // Reset form fields
        document.getElementById('cc-trans-merchant').value = '';
        document.getElementById('cc-trans-desc').value = '';
        document.getElementById('cc-trans-amount').value = '';
        document.getElementById('cc-trans-kind').value = 'charge';
        document.getElementById('cc-trans-owner').value = 'personal';
        document.getElementById('cc-trans-trip').value = '';
        document.getElementById('cc-trans-recurring').checked = false;
        document.getElementById('cc-recurring-day-group').classList.add('hidden');
        document.getElementById('cc-trans-recurring-day').value = '';
    });

    // Add charges directly from the card list view.
    document.getElementById('cc-list-add-form').addEventListener('submit', (e) => {
        e.preventDefault();
        const cardId = state.ccSelectedCardId;
        const date = document.getElementById('cc-list-add-date').value;
        const merchant = document.getElementById('cc-list-add-merchant').value.trim();
        const description = document.getElementById('cc-list-add-desc').value.trim();
        const amount = parseFloat(document.getElementById('cc-list-add-amount').value);
        const kind = document.getElementById('cc-list-add-kind').value;
        const owner = document.getElementById('cc-list-add-owner').value;
        const trip = document.getElementById('cc-list-add-trip').value.trim();
        if (!cardId || !date || !description || !Number.isFinite(amount) || amount <= 0) return;

        const dateObj = new Date(date + 'T00:00:00');
        const y = dateObj.getFullYear();
        const mShort = MONTH_ORDER[dateObj.getMonth()];
        const key = `${y}-${mShort}`;
        if (!state.cardCalendars) state.cardCalendars = {};
        if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
        if (!state.cardCalendars[cardId][key]) state.cardCalendars[cardId][key] = [];

        const activeCard = state.loans.find(l => l.id === cardId);

        if (kind === 'payment') {
            const source = owner;
            const linkId = 'manual-pmt-' + Math.random().toString(36).substr(2, 9);
            ensureYearMonthInitialized(y, mShort);
            const checkingTxId = (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9);
            const pmtDesc = `Pmt: ${activeCard ? activeCard.name : 'Card'}`;
            if (source === 'personal') {
                state.personalCalendar[key].push({
                    id: checkingTxId, date, description: pmtDesc,
                    amount: -Math.abs(amount), linkedPaymentId: linkId, payoffTargetId: cardId
                });
            } else {
                state.jointRegister.push({
                    id: checkingTxId, date, name: pmtDesc, description: pmtDesc,
                    amount: -Math.abs(amount), linkedPaymentId: linkId, payoffTargetId: cardId
                });
            }
            state.cardCalendars[cardId][key].push({
                id: 'c-' + Math.random().toString(36).substr(2, 9), date,
                description: `Payment from ${source === 'joint' ? 'Joint' : 'Personal'} Checking`,
                amount: Math.abs(amount), transactionKind: 'payment', owner: source,
                linkedPaymentId: linkId, payoffTargetId: cardId
            });
            if (activeCard) activeCard.currentBal = Math.max(0, activeCard.currentBal - amount);
            saveDatabase();
            e.target.reset();
            document.getElementById('cc-list-add-date').value = date;
            renderCardDashboard(cardId);
            logSuccess(`Payment of $${amount.toFixed(2)} to ${activeCard ? activeCard.name : 'Card'} recorded from ${source === 'joint' ? 'Joint' : 'Personal'} Checking.`);
            return;
        }

        const signedAmount = kind === 'credit' ? Math.abs(amount) : -Math.abs(amount);

        state.cardCalendars[cardId][key].push({
            id: 'c-' + Math.random().toString(36).substr(2, 9),
            date, merchant, description, amount: signedAmount,
            transactionKind: kind, owner, trip,
            isRecurring: false, recurringDay: 0, recurringSeriesId: ''
        });
        adjustCardCurrentBalance(cardId, signedAmount);
        saveDatabase();
        e.target.reset();
        document.getElementById('cc-list-add-date').value = date;
        renderCardDashboard(cardId);
        logSuccess(`Added ${owner} card ${kind}: ${description} ($${amount.toFixed(2)})${trip ? ` for ${trip}` : ''}.`);
    });

    ['cc-list-filter-text', 'cc-list-filter-merchant', 'cc-list-filter-owner', 'cc-list-filter-trip'].forEach(id => {
        document.getElementById(id).addEventListener('input', () => {
            if (state.ccSelectedCardId) renderCCCardList(state.ccSelectedCardId);
        });
    });
    document.getElementById('btn-clear-cc-filters').addEventListener('click', () => {
        document.getElementById('cc-list-filter-text').value = '';
        document.getElementById('cc-list-filter-merchant').value = 'all';
        document.getElementById('cc-list-filter-owner').value = 'all';
        document.getElementById('cc-list-filter-trip').value = 'all';
        if (state.ccSelectedCardId) renderCCCardList(state.ccSelectedCardId);
    });


    document.getElementById('btn-calculate-payoff').addEventListener('click', () => {
        const card = state.loans.find(item => item.id === state.ccSelectedCardId);
        const targetDate = document.getElementById('payoff-target-date').value;
        const months = monthsUntilDate(targetDate);
        if (!card || !targetDate || months < 1) {
            alert('Choose a payoff date at least one month in the future.');
            return;
        }
        card.payoffTargetDate = targetDate;
        card.payoffSource = document.getElementById('payoff-source').value;
        card.payoffSuggestedAmount = Math.ceil(calculateMonthlyPayoff(calculateCardLedgerBalance(card.id), card, months) * 100) / 100;
        saveDatabase();
        renderCardPayoffWidgets(card);
    });

    document.getElementById('btn-apply-payoff-plan').addEventListener('click', () => {
        const card = state.loans.find(item => item.id === state.ccSelectedCardId);
        if (!card?.payoffSuggestedAmount || !card.payoffTargetDate) return;
        const message = `Schedule ${monthsUntilDate(card.payoffTargetDate)} future monthly payments of $${card.payoffSuggestedAmount.toFixed(2)} to ${card.name}? Existing generated payoff-plan payments for this card will be replaced.`;
        if (!confirm(message)) return;
        scheduleCardPayoffPlan(card, card.payoffSuggestedAmount, card.payoffTargetDate, document.getElementById('payoff-source').value);
        renderApp();
        logSuccess(`Scheduled monthly payoff payments for ${card.name} through ${card.payoffTargetDate}.`);
    });
}

// Keeps a card payment's linked checking-side entry in sync after editing the payment from the
// credit card ledger — date, amount, description, AND which ledger it lives in. Previously this only
// updated date/amount in place and never moved the entry, so changing a payment's Ownership from
// Personal to Joint (or back) left a stale entry in the old ledger and orphaned it there permanently.
function syncLinkedPayoffPayment(cardTx) {
    if (!cardTx.linkedPaymentId) return;
    let linked = null;

    for (const list of Object.values(state.personalCalendar || {})) {
        const index = list.findIndex(tx => tx.linkedPaymentId === cardTx.linkedPaymentId);
        if (index > -1) { linked = list.splice(index, 1)[0]; break; }
    }
    if (!linked) {
        const index = state.jointRegister.findIndex(tx => tx.linkedPaymentId === cardTx.linkedPaymentId);
        if (index > -1) linked = state.jointRegister.splice(index, 1)[0];
    }
    if (!linked) return;

    // The checking-side label reads "Pmt: <Card Name>" while the card-side entry's own description
    // reads "Payment from Personal/Joint Checking" — these describe the same payment from two
    // different vantage points and are not interchangeable, so re-derive the checking-side label
    // from the card rather than copying cardTx.description over it.
    const linkedCard = state.loans.find(l => l.id === cardTx.payoffTargetId);
    const checkingDescription = linkedCard ? `Pmt: ${linkedCard.name}` : linked.description;

    linked.date = cardTx.date;
    linked.amount = -Math.abs(cardTx.amount);
    linked.description = checkingDescription;

    if (cardTx.owner === 'joint') {
        linked.name = checkingDescription;
        state.jointRegister.push(linked);
    } else {
        const dateObj = new Date(cardTx.date + 'T00:00:00');
        const targetKey = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
        ensureYearMonthInitialized(dateObj.getFullYear(), MONTH_ORDER[dateObj.getMonth()]);
        if (!state.personalCalendar[targetKey]) state.personalCalendar[targetKey] = [];
        state.personalCalendar[targetKey].push(linked);
    }
}
function syncCheckingPaymentToCard(checkingTx) {
    if (!checkingTx.linkedPaymentId) return;
    
    let cardTx = null;
    let cardIdFound = '';
    let origKey = '';
    
    for (const [cId, calendar] of Object.entries(state.cardCalendars || {})) {
        for (const [key, list] of Object.entries(calendar || {})) {
            const index = list.findIndex(tx => tx.linkedPaymentId === checkingTx.linkedPaymentId);
            if (index > -1) {
                cardTx = list[index];
                cardIdFound = cId;
                origKey = key;
                break;
            }
        }
        if (cardTx) break;
    }
    
    if (cardTx && cardIdFound) {
        const oldAmt = cardTx.amount;
        const newAmt = Math.abs(checkingTx.amount);
        cardTx.date = checkingTx.date;
        cardTx.amount = newAmt;
        
        const cardObj = state.loans.find(l => l.id === cardIdFound);
        if (cardObj) {
            cardObj.currentBal = Math.max(0, cardObj.currentBal + oldAmt - newAmt);
        }
        
        const dateObj = new Date(checkingTx.date + 'T00:00:00');
        const targetKey = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
        if (origKey !== targetKey) {
            state.cardCalendars[cardIdFound][origKey] = state.cardCalendars[cardIdFound][origKey].filter(tx => tx.linkedPaymentId !== checkingTx.linkedPaymentId);
            if (!state.cardCalendars[cardIdFound][targetKey]) state.cardCalendars[cardIdFound][targetKey] = [];
            state.cardCalendars[cardIdFound][targetKey].push(cardTx);
        }
    }
}
function syncAutomaticCardPaymentOverride(cardTx, cardId) {
    if (!cardTx.isAutomaticCardPayment || !cardTx.automaticPaymentId) return;
    const linkId = cardTx.automaticPaymentId;
    let linked = null;
    Object.values(state.personalCalendar || {}).forEach(list => {
        const index = list.findIndex(tx => tx.automaticPaymentId === linkId);
        if (index > -1) linked = list.splice(index, 1)[0];
    });
    const jointIndex = state.jointRegister.findIndex(tx => tx.automaticPaymentId === linkId);
    if (jointIndex > -1) linked = state.jointRegister.splice(jointIndex, 1)[0];

    const source = cardTx.owner === 'joint' ? 'joint' : 'personal';
    const dateObj = new Date(cardTx.date + 'T00:00:00');
    const month = MONTH_ORDER[dateObj.getMonth()];
    const key = `${dateObj.getFullYear()}-${month}`;
    ensureYearMonthInitialized(dateObj.getFullYear(), month);
    const card = state.loans.find(item => item.id === cardId);
    const checkingTx = {
        ...(linked || {}),
        id: linked?.id || (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9),
        type: source === 'joint' ? 'expense' : undefined,
        name: `Pmt: ${card?.name || 'Credit Card'}`,
        description: `Pmt: ${card?.name || 'Credit Card'}`,
        date: cardTx.date,
        amount: -Math.abs(cardTx.amount),
        automaticPaymentId: linkId,
        isAutomaticCardPayment: true,
        automaticPaymentOverridden: true,
        payoffTargetId: cardId
    };
    if (source === 'joint') state.jointRegister.push(checkingTx);
    else state.personalCalendar[key].push(checkingTx);
}
function clearFutureAutomaticCardPayments(cardId, fromDate = formatLocalDate(new Date())) {
    const cardCal = state.cardCalendars?.[cardId] || {};
    const removedLinkIds = new Set();
    Object.values(cardCal).forEach(list => {
        for (let i = list.length - 1; i >= 0; i--) {
            const tx = list[i];
            if (tx.isAutomaticCardPayment && !tx.automaticPaymentOverridden && tx.date >= fromDate) {
                removedLinkIds.add(tx.automaticPaymentId);
                list.splice(i, 1);
            }
        }
    });
    Object.values(state.personalCalendar || {}).forEach(list => {
        for (let i = list.length - 1; i >= 0; i--) if (removedLinkIds.has(list[i].automaticPaymentId)) list.splice(i, 1);
    });
    for (let i = state.jointRegister.length - 1; i >= 0; i--) {
        if (removedLinkIds.has(state.jointRegister[i].automaticPaymentId)) state.jointRegister.splice(i, 1);
    }
}

function getStatementClosingDateForPayment(card, dueDate) {
    const due = new Date(dueDate + 'T00:00:00');
    const statementDay = Math.min(31, Math.max(1, Number(card.statementDay) || 1));
    let closingYear = due.getFullYear();
    let closingMonth = due.getMonth();
    let closingDay = Math.min(statementDay, new Date(closingYear, closingMonth + 1, 0).getDate());
    let closing = new Date(closingYear, closingMonth, closingDay);
    if (closing >= due) {
        closingMonth -= 1;
        if (closingMonth < 0) { closingMonth = 11; closingYear -= 1; }
        closingDay = Math.min(statementDay, new Date(closingYear, closingMonth + 1, 0).getDate());
        closing = new Date(closingYear, closingMonth, closingDay);
    }
    return `${closing.getFullYear()}-${String(closing.getMonth() + 1).padStart(2, '0')}-${String(closing.getDate()).padStart(2, '0')}`;
}
function ensureAutomaticCardPaymentForMonth(cardId, year, month) {
    const card = state.loans.find(item => item.id === cardId);
    if (!card) return;
    const isLoan = card.type === 'loan';
    // Installment loans always pay automatically (no opt-out strategy — every loan payment is
    // recurring by design); credit cards keep their existing opt-in payment strategy.
    const strategy = isLoan ? 'loanMinimum' : (card.paymentStrategy || 'none');
    if (!isLoan && strategy === 'none') return;

    const monthIndex = MONTH_ORDER.indexOf(month);
    const daysInMonth = new Date(year, monthIndex + 1, 0).getDate();
    const dueDay = Math.min(Number(card.dueDay) || 1, daysInMonth);
    const dueDate = `${year}-${String(monthIndex + 1).padStart(2, '0')}-${String(dueDay).padStart(2, '0')}`;
    // First payment date applies to both credit cards and installment loans (loans always auto-pay,
    // so this is the only way to delay a loan's first automatic payment).
    if (card.paymentStrategyStartDate && dueDate < card.paymentStrategyStartDate) return;
    if (card.paymentEndDate && dueDate > card.paymentEndDate) return;

    const key = `${year}-${month}`;
    if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
    if (!state.cardCalendars[cardId][key]) state.cardCalendars[cardId][key] = [];
    const cardList = state.cardCalendars[cardId][key];
    const existingIndex = cardList.findIndex(tx => tx.isAutomaticCardPayment);
    let linkId = `autopay-${cardId}-${year}-${String(monthIndex + 1).padStart(2, '0')}`;
    let existingPayment = null;
    if (existingIndex > -1) {
        existingPayment = cardList[existingIndex];
        linkId = existingPayment.automaticPaymentId || linkId;
        if (existingPayment.automaticPaymentOverridden) {
            syncAutomaticCardPaymentOverride(existingPayment, cardId);
            return;
        }
        // Temporarily remove so the balance calculations below don't count the payment itself.
        cardList.splice(existingIndex, 1);
    }

    const balanceAtDueDate = calculateCardLedgerBalance(cardId, dueDate);
    let amount = 0;
    let statementClosingDate = '';
    let statementTransactionCutoffDate = '';
    if (isLoan) {
        // Loans have no statement cycle — just pay the fixed monthly minimum against the current
        // balance, capped so the final payment doesn't overpay.
        amount = Math.min(balanceAtDueDate, Number(card.monthlyMin) || 0);
    } else {
        statementClosingDate = getStatementClosingDateForPayment(card, dueDate);
        const statementCutoff = new Date(statementClosingDate + 'T00:00:00');
        statementCutoff.setDate(statementCutoff.getDate() - 1);
        statementTransactionCutoffDate = `${statementCutoff.getFullYear()}-${String(statementCutoff.getMonth() + 1).padStart(2, '0')}-${String(statementCutoff.getDate()).padStart(2, '0')}`;
        const closedStatementBalance = calculateCardLedgerBalance(cardId, statementTransactionCutoffDate);
        if (strategy === 'balance') amount = closedStatementBalance;
        else if (strategy === 'minimum') amount = Math.min(balanceAtDueDate, Number(card.monthlyMin) || 0);
        else if (strategy === 'interestSaving') amount = Math.min(balanceAtDueDate, calculateInterestSavingPayment(card, dueDate));
    }
    amount = Math.max(0, Math.round(amount * 100) / 100);

    const source = card.paymentSource || 'personal';

    // Idempotence check: if the recomputed payment is identical to the existing one and its
    // checking-side leg still exists, put the existing transaction back untouched and stop.
    // This runs on every render of the card dashboard (12x in year scope), and the old
    // rebuild-every-time behavior churned transaction ids and triggered a full ~MBs state
    // serialization per month per render — the source of the slow month-to-month navigation.
    if (existingPayment && amount > 0
        && existingPayment.date === dueDate
        && Math.abs((Number(existingPayment.amount) || 0) - amount) < 0.005
        && (existingPayment.owner || 'personal') === source) {
        const checkingLegExists = source === 'joint'
            ? state.jointRegister.some(tx => tx.automaticPaymentId === linkId)
            : Object.values(state.personalCalendar || {}).some(list => (list || []).some(tx => tx.automaticPaymentId === linkId));
        if (checkingLegExists) {
            cardList.push(existingPayment);
            return;
        }
    }

    Object.values(state.personalCalendar || {}).forEach(list => {
        for (let i = list.length - 1; i >= 0; i--) if (list[i].automaticPaymentId === linkId) list.splice(i, 1);
    });
    for (let i = state.jointRegister.length - 1; i >= 0; i--) {
        if (state.jointRegister[i].automaticPaymentId === linkId) state.jointRegister.splice(i, 1);
    }

    if (amount <= 0) {
        // The existing payment (if any) is no longer warranted; persist its removal.
        if (existingPayment) saveDatabase();
        return;
    }

    const checkingTx = {
        id: (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9),
        type: source === 'joint' ? 'expense' : undefined,
        name: `Pmt: ${card.name}`,
        description: `Pmt: ${card.name}`,
        date: dueDate,
        amount: -amount,
        automaticPaymentId: linkId,
        isAutomaticCardPayment: true,
        payoffTargetId: cardId
    };
    ensureYearMonthInitialized(year, month);
    if (source === 'joint') state.jointRegister.push(checkingTx);
    else state.personalCalendar[key].push(checkingTx);

    cardList.push({
        id: 'c-' + Math.random().toString(36).substr(2, 9),
        date: dueDate,
        description: isLoan ? 'Automatic Monthly Payment' : `Automatic ${strategy === 'balance' ? 'Full Balance' : strategy === 'minimum' ? 'Minimum' : 'Interest-Saving'} Payment`,
        amount,
        transactionKind: 'payment',
        owner: source,
        automaticPaymentId: linkId,
        isAutomaticCardPayment: true,
        statementClosingDate: strategy === 'balance' ? statementClosingDate : '',
        statementTransactionCutoffDate: strategy === 'balance' ? statementTransactionCutoffDate : ''
    });
    saveDatabase();
}
function renderCardPayoffWidgets(card) {
    const balance = calculateCardLedgerBalance(card.id);
    const apr = getEffectiveCardRateForMonth(card, 0);
    const minimum = Number(card.monthlyMin) || 0;
    const minMonths = estimatePayoffMonths(balance, card, minimum);

    document.getElementById('payoff-current-balance').textContent = formatCardBalance(balance);
    document.getElementById('payoff-apr').textContent = `${apr.toFixed(2)}%`;
    document.getElementById('payoff-minimum').textContent = `$${minimum.toFixed(2)}`;
    document.getElementById('payoff-min-estimate').textContent = Number.isFinite(minMonths)
        ? `${minMonths} month${minMonths === 1 ? '' : 's'}`
        : 'Payment too low';

    const targetInput = document.getElementById('payoff-target-date');
    if (card.payoffTargetDate) targetInput.value = card.payoffTargetDate;
    document.getElementById('payoff-source').value = card.payoffSource || 'personal';

    const planSummary = document.getElementById('card-payment-plans-summary-list');
    const plans = (card.paymentPlans || []).map(normalizePaymentPlan).filter(plan => plan.currentBalance > 0);
    planSummary.innerHTML = plans.length ? `
        <div class="table-responsive"><table class="data-table"><thead><tr><th>Plan</th><th>Activated</th><th>Payments Left</th><th>Original</th><th>Remaining</th><th>Principal / Month</th><th>Monthly Fee</th><th>Projected Payoff</th></tr></thead><tbody>
        ${plans.map(plan => `<tr><td>${escapeHTML(plan.name)}</td><td>${plan.startDate || '—'}</td><td>${plan.remainingPayments}</td><td>$${plan.originalAmount.toFixed(2)}</td><td>$${plan.currentBalance.toFixed(2)}</td><td>$${plan.monthlyPayment.toFixed(2)}</td><td>$${plan.monthlyFee.toFixed(2)}</td><td>${plan.payoffDate || 'TBD'}</td></tr>`).join('')}
        </tbody></table></div>` : '<p class="muted-text">No active payment plans. Convert a charge by editing it, or add an existing plan in Card Details.</p>';

    const suggestion = document.getElementById('payoff-suggestion');
    const applyButton = document.getElementById('btn-apply-payoff-plan');
    if (card.payoffSuggestedAmount && card.payoffTargetDate) {
        suggestion.textContent = `$${card.payoffSuggestedAmount.toFixed(2)} / month for ${monthsUntilDate(card.payoffTargetDate)} months`;
        applyButton.disabled = false;
    } else {
        suggestion.textContent = 'Choose a target date.';
        applyButton.disabled = true;
    }
}

function scheduleCardPayoffPlan(card, amount, targetDate, source) {
    const todayStr = formatLocalDate(new Date());
    const isThisPlan = tx => tx.isPayoffPlan && tx.payoffTargetId === card.id && tx.date > todayStr;

    Object.values(state.personalCalendar || {}).forEach(list => {
        for (let i = list.length - 1; i >= 0; i--) if (isThisPlan(list[i])) list.splice(i, 1);
    });
    for (let i = state.jointRegister.length - 1; i >= 0; i--) {
        if (isThisPlan(state.jointRegister[i])) state.jointRegister.splice(i, 1);
    }
    Object.values(state.cardCalendars?.[card.id] || {}).forEach(list => {
        for (let i = list.length - 1; i >= 0; i--) if (isThisPlan(list[i])) list.splice(i, 1);
    });

    const months = monthsUntilDate(targetDate);
    const today = new Date();
    for (let offset = 1; offset <= months; offset++) {
        const paymentMonth = new Date(today.getFullYear(), today.getMonth() + offset, 1);
        const daysInMonth = new Date(paymentMonth.getFullYear(), paymentMonth.getMonth() + 1, 0).getDate();
        paymentMonth.setDate(Math.min(Number(card.dueDay) || 1, daysInMonth));
        const date = `${paymentMonth.getFullYear()}-${String(paymentMonth.getMonth() + 1).padStart(2, '0')}-${String(paymentMonth.getDate()).padStart(2, '0')}`;
        const month = MONTH_ORDER[paymentMonth.getMonth()];
        const key = `${paymentMonth.getFullYear()}-${month}`;
        const linkId = 'plan-' + Math.random().toString(36).substr(2, 9);
        ensureYearMonthInitialized(paymentMonth.getFullYear(), month);

        const checkingTx = {
            id: (source === 'joint' ? 'j-' : 'p-') + Math.random().toString(36).substr(2, 9),
            type: source === 'joint' ? 'expense' : undefined,
            name: `Pmt: ${card.name}`,
            description: `Pmt: ${card.name}`,
            date,
            amount: -Math.abs(amount),
            isPayoffPlan: true,
            payoffTargetId: card.id,
            linkedPaymentId: linkId
        };
        if (source === 'joint') state.jointRegister.push(checkingTx);
        else state.personalCalendar[key].push(checkingTx);

        if (!state.cardCalendars[card.id]) state.cardCalendars[card.id] = {};
        if (!state.cardCalendars[card.id][key]) state.cardCalendars[card.id][key] = [];
        state.cardCalendars[card.id][key].push({
            id: 'c-' + Math.random().toString(36).substr(2, 9),
            date,
            description: `Payment from ${source === 'joint' ? 'Joint' : 'Personal'} Checking`,
            amount: Math.abs(amount),
            owner: source,
            isPayoffPlan: true,
            payoffTargetId: card.id,
            linkedPaymentId: linkId
        });
    }

    card.payoffTargetDate = targetDate;
    card.payoffSuggestedAmount = amount;
    card.payoffSource = source;
    saveDatabase();
}
function populateChargeAutocomplete(cardId) {
    const cardCal = state.cardCalendars?.[cardId] || {};
    const transactions = Object.values(cardCal)
        .flatMap(list => list || [])
        .filter(tx => tx && tx.amount < 0)
        .sort((a, b) => (b.date || '').localeCompare(a.date || ''));

    const uniqueRecentValues = field => {
        const seen = new Set();
        const values = [];
        transactions.forEach(tx => {
            const value = String(tx[field] || '').trim();
            const normalized = value.toLocaleLowerCase();
            if (value && !seen.has(normalized)) {
                seen.add(normalized);
                values.push(value);
            }
        });
        return values;
    };

    const fillDatalist = (id, values) => {
        const list = document.getElementById(id);
        list.replaceChildren();
        values.forEach(value => {
            const option = document.createElement('option');
            option.value = value;
            list.appendChild(option);
        });
    };

    fillDatalist('cc-merchant-suggestions', uniqueRecentValues('merchant'));
    fillDatalist('cc-description-suggestions', uniqueRecentValues('description'));
}
function renderCardDashboard(cardId) {
    const card = state.loans.find(c => c.id === cardId);
    if (!card) return;

    if (state.ccViewMode === 'list' && state.ccListScope === 'year') {
        MONTH_ORDER.forEach(month => {
            ensureRecurringCardChargesForMonth(cardId, state.ccYear, month);
            ensureAutomaticCardPaymentForMonth(cardId, state.ccYear, month);
        });
    } else {
        ensureRecurringCardChargesForMonth(cardId, state.ccYear, state.ccMonth);
        ensureAutomaticCardPaymentForMonth(cardId, state.ccYear, state.ccMonth);
    }
    populateChargeAutocomplete(cardId);

    // The opening balance plus posted ledger activity is the source of truth for current debt.
    card.currentBal = calculateCardLedgerBalance(cardId);
    renderCardPayoffWidgets(card);
    
const limit = card.limit || 5000;
    const utilPct = card.isChargeCard ? null : ((card.currentBal / limit) * 100).toFixed(0);
    const accountSummary = card.isChargeCard
        ? `Charge Card | Balance: $${card.currentBal.toFixed(2)} | No preset limit`
        : `Limit: $${limit.toFixed(0)} | Balance: $${card.currentBal.toFixed(2)} (${utilPct}% used)`;
    document.getElementById('cc-dashboard-title').innerHTML = `
        ${escapeHTML(card.name)} Dashboard
        <span style="font-size: 0.8rem; font-weight: normal; margin-left: 0.75rem; background: rgba(255,255,255,0.06); padding: 2px 8px; border-radius: 4px; color: var(--text-secondary);">
            ${accountSummary}
        </span>
    `;
    // Sync View Toggle active states
    document.querySelectorAll('#cc-view-toggle .segment-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.mode === state.ccViewMode);
    });
    document.getElementById('cc-calendar-view-container').classList.toggle('hidden', state.ccViewMode === 'list');
    document.getElementById('cc-list-view-container').classList.toggle('hidden', state.ccViewMode === 'calendar');
    document.getElementById('cc-scope-toggle').classList.toggle('hidden', state.ccViewMode === 'calendar');
    
    if (state.ccViewMode === 'list') {
        document.querySelectorAll('#cc-scope-toggle .segment-btn').forEach(btn => {
            btn.classList.toggle('active', btn.dataset.scope === state.ccListScope);
        });
        renderCCCardList(cardId);
        return;
    }
    
    const year = state.ccYear;
    const month = state.ccMonth;
    const monthIndex = MONTH_ORDER.indexOf(month);
    const ccDaysContainer = document.getElementById('cc-calendar-days');
    ccDaysContainer.innerHTML = '';
    
    // Compute date grid
    const firstDay = new Date(Date.UTC(year, monthIndex, 1));
    const startDayOfWeek = firstDay.getUTCDay();
    const gridStart = new Date(firstDay);
    gridStart.setUTCDate(gridStart.getUTCDate() - startDayOfWeek);
    
    const totalCells = 42;
    const daysData = [];
    const tempDate = new Date(gridStart);
    for (let i = 0; i < totalCells; i++) {
        const dateStr = tempDate.toISOString().split('T')[0];
        const isCurrentMonth = tempDate.getUTCMonth() === monthIndex;
        daysData.push({
            date: dateStr,
            dayNum: tempDate.getUTCDate(),
            isCurrentMonth: isCurrentMonth,
            transactions: []
        });
        tempDate.setUTCDate(tempDate.getUTCDate() + 1);
    }
    
    let dbModified = false;
    daysData.forEach(day => {
        const cellDateObj = new Date(day.date + 'T00:00:00');
        const cellYear = cellDateObj.getFullYear();
        const cellMonth = MONTH_ORDER[cellDateObj.getMonth()];
        const cellKey = `${cellYear}-${cellMonth}`;
        
        ensureYearMonthInitialized(cellYear, cellMonth);
        
        const cellTxList = (state.cardCalendars && state.cardCalendars[cardId]) ? (state.cardCalendars[cardId][cellKey] || []) : [];
        const matchedTx = cellTxList.filter(tx => tx.date === day.date && !tx.billOccurrenceDeleted);
        matchedTx.forEach(tx => {
            if (!tx.id) {
                tx.id = 'c-' + Math.random().toString(36).substr(2, 9);
                dbModified = true;
            }
            day.transactions.push({
                id: tx.id,
                merchant: tx.merchant || '',
                description: tx.description,
                amount: tx.amount,
                type: tx.amount >= 0 ? 'income' : 'expense',
                transactionKind: tx.transactionKind || (tx.amount < 0 ? 'charge' : 'payment'),
                isRecurring: !!tx.isRecurring,
                balanceTransferBy: tx.balanceTransferBy || ''
            });
        });
    });
    if (dbModified) saveDatabase();
    
    // Sort & calculate running debt owed
    let runningBalance = getCardRunningBalanceAtDate(cardId, daysData[0].date);
    daysData.forEach(day => {
        day.transactions.sort((a, b) => b.amount - a.amount);
        day.transactions.forEach(t => {
            if (t.amount < 0) {
                runningBalance += Math.abs(t.amount);
            } else {
                runningBalance -= t.amount;
            }
        });
        day.balance = runningBalance;
    });
    
    // Draw cells
    daysData.forEach(day => {
        const dayCell = document.createElement('div');
        const todayStr = formatLocalDate(new Date());
        dayCell.className = `calendar-day ${day.isCurrentMonth ? '' : 'next-month'} ${day.date === state.ccSelectedDate ? 'selected-day' : ''}${day.date === todayStr ? ' today-highlight' : ''}`;
        dayCell.dataset.date = day.date;
        
        const balanceColorClass = day.balance > 0.01 ? 'negative' : 'positive';
        
        let txsHtml = '';
        day.transactions.slice(0, 3).forEach(t => {
            const typeClass = t.amount < 0 ? 'expense' : 'income';
            const displayLabel = escapeHTML(getTransactionIndicatorPrefix(t) + (t.merchant ? t.merchant : t.description));
            txsHtml += `
                <div class="day-transaction-item ${typeClass}"
                     title="${t.isRecurring ? '[Recurring] ' : ''}${t.merchant ? escapeHTML(t.merchant) + ' - ' : ''}${escapeHTML(t.description)}: $${t.amount.toFixed(2)}${getClassificationTooltipSuffix(t)}"
                     draggable="true"
                     data-id="${t.id}"
                     data-date="${day.date}">
                    <span>${displayLabel}</span>
                    <span>${t.amount >= 0 ? '+' : ''}${Math.round(t.amount)}</span>
                </div>
            `;
        });
        if (day.transactions.length > 3) {
            txsHtml += `<div class="day-transaction-item muted-text" style="background:none; text-align:center;">+${day.transactions.length - 3} more</div>`;
        }
        
        dayCell.innerHTML = `
            <div class="day-number-wrapper">
                <span class="day-number">${day.dayNum}</span>
                <span class="day-balance ${balanceColorClass}" title="Double-click to reconcile">$${Math.round(day.balance)}</span>
            </div>
            <div class="day-transactions">
                ${txsHtml}
            </div>
        `;
        
        // Drag start/end/edit bindings
        dayCell.querySelectorAll('.day-transaction-item').forEach(txItem => {
            txItem.addEventListener('dragstart', (e) => {
                e.dataTransfer.setData('text/plain', JSON.stringify({
                    id: txItem.dataset.id,
                    date: txItem.dataset.date
                }));
                txItem.classList.add('dragging');
            });
            txItem.addEventListener('dragend', () => {
                txItem.classList.remove('dragging');
            });
            txItem.addEventListener('dblclick', (e) => {
                e.stopPropagation();
                openEditTransactionModal(txItem.dataset.id, txItem.dataset.date);
            });
        });
        
        // Drag over / drops
        dayCell.addEventListener('dragover', (e) => e.preventDefault());
        dayCell.addEventListener('dragenter', (e) => { e.preventDefault(); dayCell.classList.add('drag-hover'); });
        dayCell.addEventListener('dragleave', () => dayCell.classList.remove('drag-hover'));
        dayCell.addEventListener('drop', (e) => {
            dayCell.classList.remove('drag-hover');
            const dataStr = e.dataTransfer.getData('text/plain');
            if (dataStr) {
                try {
                    const data = JSON.parse(dataStr);
                    moveCCSubTransaction(cardId, data.id, data.date, day.date);
                } catch(err) {
                    console.error("CC drop parse error:", err);
                }
            }
        });
        
        // Click to select date
        dayCell.addEventListener('click', () => {
            document.querySelectorAll('#cc-calendar-days .calendar-day').forEach(c => c.classList.remove('selected-day'));
            dayCell.classList.add('selected-day');
            state.ccSelectedDate = day.date;
            document.getElementById('cc-trans-date').value = day.date;
        });
        dayCell.querySelector('.day-number').addEventListener('click', (e) => {
            e.stopPropagation();
            dayCell.click();
            renderCCDayHighlights(cardId, day);
            showDayHighlightsDialog('cc-today-highlights-list');
        });
        
        ccDaysContainer.appendChild(dayCell);
    });
}

function moveCCSubTransaction(cardId, txId, sourceDate, targetDate) {
    if (sourceDate === targetDate) return;
    
    const srcObj = new Date(sourceDate + 'T00:00:00');
    const srcKey = `${srcObj.getFullYear()}-${MONTH_ORDER[srcObj.getMonth()]}`;
    const tgtObj = new Date(targetDate + 'T00:00:00');
    const tgtKey = `${tgtObj.getFullYear()}-${MONTH_ORDER[tgtObj.getMonth()]}`;
    
    if (!state.cardCalendars) state.cardCalendars = {};
    if (!state.cardCalendars[cardId]) state.cardCalendars[cardId] = {};
    
    const srcList = state.cardCalendars[cardId][srcKey] || [];
    const tx = srcList.find(t => t.id === txId);
    if (tx) {
        tx.date = targetDate;
        if (srcKey !== tgtKey) {
            const idx = srcList.indexOf(tx);
            srcList.splice(idx, 1);
            if (!state.cardCalendars[cardId][tgtKey]) state.cardCalendars[cardId][tgtKey] = [];
            state.cardCalendars[cardId][tgtKey].push(tx);
        }
        logSuccess(`Moved card transaction to ${targetDate}: ${tx.description}`);
        saveDatabase();
        renderCardDashboard(cardId);
    }
}

function renderCCDayHighlights(cardId, day) {
    const list = document.getElementById('cc-today-highlights-list');
    list.innerHTML = '';
    
    const formattedDate = new Date(day.date + 'T00:00:00').toLocaleDateString('en-US', {
        weekday: 'long', year: 'numeric', month: 'long', day: 'numeric'
    });
    
    const headerHtml = `
        <div style="margin-bottom: 0.5rem;">
            <strong>${formattedDate}</strong>
            <div style="font-size: 0.85rem; color: var(--text-secondary); margin-top: 2px;">Owed Balance: $${day.balance.toFixed(2)}</div>
        </div>
    `;
    list.insertAdjacentHTML('beforeend', headerHtml);
    
    if (day.transactions.length === 0) {
        list.insertAdjacentHTML('beforeend', `<p class="muted-text">No transactions logged for this day.</p>`);
        return;
    }
    
    day.transactions.forEach(t => {
        const isCharge = t.amount < 0;
        const prefix = t.amount >= 0 ? '+' : '';
        const merchantLabel = t.merchant ? `<span style="font-size:0.8rem; color:var(--text-secondary); margin-left:0.5rem; background:rgba(255,255,255,0.04); padding:1px 6px; border-radius:3px;">${escapeHTML(t.merchant)}</span>` : '';

        const itemHtml = document.createElement('div');
        itemHtml.className = 'highlight-item';
        itemHtml.style.cursor = 'pointer';
        itemHtml.title = 'Double-click to edit';
        itemHtml.innerHTML = `
            <div class="highlight-item-left">
                <span class="highlight-item-title">${escapeHTML(t.description)}${merchantLabel}${getTransactionIndicatorBadges(t)}</span>
                <span class="highlight-item-tag">${isCharge ? 'CHARGE' : (t.transactionKind === 'credit' ? 'CREDIT / REVERSAL' : 'PAYMENT')}</span>
            </div>
            <div style="display: flex; align-items: center; gap: 0.75rem;">
                <span class="highlight-item-amount ${isCharge ? 'negative' : 'positive'}">${prefix}$${t.amount.toFixed(2)}</span>
                <button class="action-btn small-btn danger-btn delete-tx-btn" data-date="${day.date}" data-id="${t.id}">Delete</button>
            </div>
        `;
        
        itemHtml.addEventListener('dblclick', () => {
            openEditTransactionModal(t.id, day.date);
        });
        
        itemHtml.querySelector('.delete-tx-btn').addEventListener('click', (e) => {
            e.stopPropagation();
            const dId = e.target.dataset.id;
            const dateObj = new Date(day.date + 'T00:00:00');
            const key = `${dateObj.getFullYear()}-${MONTH_ORDER[dateObj.getMonth()]}`;
            
            const list = state.cardCalendars[cardId][key] || [];
            const idx = list.findIndex(tx => tx.id === dId);
            if (idx > -1) {
                const removed = deleteCardTransactionWithRecurringChoice(cardId, key, dId);
                if (!removed) return;
                adjustCardCurrentBalance(cardId, removed.amount, -1);
                saveDatabase();
                renderCardDashboard(cardId);
                logSystem(`Deleted credit card transaction on ${day.date}: ${removed.description}`);
            }
        });
        
        list.appendChild(itemHtml);
    });
}

function renderCCCardList(cardId) {
    const card = state.loans.find(c => c.id === cardId);
    if (!card) return;

    const container = document.getElementById('cc-list-view-table-container');
    const year = state.ccYear;
    const cardCal = state.cardCalendars[cardId] || {};
    const textFilter = document.getElementById('cc-list-filter-text').value.trim().toLowerCase();
    const merchantSelect = document.getElementById('cc-list-filter-merchant');
    const tripSelect = document.getElementById('cc-list-filter-trip');
    const merchantFilter = merchantSelect.value || 'all';
    const ownerFilter = document.getElementById('cc-list-filter-owner').value;
    const tripFilter = tripSelect.value || 'all';

    let txList = [];
    if (state.ccListScope === 'month') {
        const key = `${year}-${state.ccMonth}`;
        (cardCal[key] || []).forEach(t => { if (!t.billOccurrenceDeleted) txList.push({ ...t, monthKey: key }); });
    } else {
        Object.keys(cardCal).forEach(key => {
            if (key.startsWith(`${year}-`)) {
                (cardCal[key] || []).forEach(t => { if (!t.billOccurrenceDeleted) txList.push({ ...t, monthKey: key }); });
            }
        });
    }

    // Populate dropdowns from the unfiltered transactions in the active scope.
    const populateFilter = (select, values, allLabel, selectedValue) => {
        select.replaceChildren();
        const allOption = document.createElement('option');
        allOption.value = 'all';
        allOption.textContent = allLabel;
        select.appendChild(allOption);
        [...new Set(values.filter(Boolean))]
            .sort((a, b) => a.localeCompare(b))
            .forEach(value => {
                const option = document.createElement('option');
                option.value = value;
                option.textContent = value;
                select.appendChild(option);
            });
        select.value = [...select.options].some(option => option.value === selectedValue) ? selectedValue : 'all';
    };
    populateFilter(merchantSelect, txList.map(t => (t.merchant || '').trim()), 'All merchants', merchantFilter);
    populateFilter(tripSelect, txList.map(t => (t.trip || '').trim()), 'All trips', tripFilter);

    txList = txList.filter(t => {
        const owner = t.owner || 'personal';
        const merchant = (t.merchant || '').trim();
        const trip = (t.trip || '').trim();
        const description = (t.description || '').toLowerCase();
        return (!textFilter || description.includes(textFilter))
            && (merchantSelect.value === 'all' || merchant === merchantSelect.value)
            && (ownerFilter === 'all' || owner === ownerFilter)
            && (tripSelect.value === 'all' || trip === tripSelect.value);
    });
    txList.sort((a, b) => new Date(a.date).getTime() - new Date(b.date).getTime());
    const { estimates, activePlans } = computeAllEstimatedBalancesForCard(cardId);
    let filteredBalance = 0;
    let filteredCharges = 0;
    let filteredPayments = 0;
    let rowsHtml = '';
    txList.forEach(t => {
        const amount = Number(t.amount) || 0;
        if (amount < 0) {
            filteredCharges += Math.abs(amount);
            filteredBalance += Math.abs(amount);
        } else {
            filteredPayments += Math.abs(amount);
            filteredBalance -= Math.abs(amount);
        }
        const dayName = new Date(t.date + 'T00:00:00').toLocaleDateString('en-US', { weekday: 'short' });
        const owner = t.owner || 'personal';
        const trip = t.trip || '';
        const merchantCell = t.merchant ? `<span style="font-weight:600;">${escapeHTML(t.merchant)}</span>` : '<span class="muted-text">-</span>';
        const recurringBadge = t.isRecurring ? '<span class="cc-recurring-badge" title="Recurring charge">&#8635; Recurring</span>' : '';
        const transferPerson = t.balanceTransferBy === 'jason' ? 'Jason' : t.balanceTransferBy === 'asia' ? 'Asia' : '';
        const transferBadge = transferPerson ? `<span class="cc-owner-badge ${t.balanceTransferBy}">Transferred by ${transferPerson}</span>` : '';

        let payoffNote = '';
        const paidOffPlan = activePlans.find(plan => plan.isPaidOff && plan.paidOffDateStr === t.date);
        if (paidOffPlan) {
            payoffNote = `<br><span style="color:#34d399; font-weight:600; font-size:0.75rem;">🎉 ${escapeHTML(paidOffPlan.name)} Paid Off (Est.)</span>`;
        }

        const estBal = (estimates[t.id] !== undefined) ? estimates[t.id] : filteredBalance;

        rowsHtml += `
            <tr class="editable-row" data-id="${t.id}" data-date="${t.date}" style="cursor: pointer;">
                <td><strong>${t.date}</strong><br><span class="muted-text">${dayName}</span></td>
                <td>${merchantCell}</td>
                <td>${escapeHTML(t.description)}${payoffNote} ${getTransactionIndicatorBadges(t)}</td>
                <td><span class="cc-owner-badge ${owner}">${owner === 'joint' ? 'Joint' : 'Personal'}</span></td>
                <td>${trip ? `<span class="cc-trip-badge">${escapeHTML(trip)}</span>` : '<span class="muted-text">-</span>'}</td>
                <td class="${amount < 0 ? 'negative' : 'positive'} font-heading">${amount >= 0 ? '+' : '-'}$${Math.abs(amount).toFixed(2)}</td>
                <td class="${filteredBalance > 0.01 ? 'negative' : 'positive'} font-heading">$${filteredBalance.toFixed(2)}</td>
                <td class="${estBal > 0.01 ? 'negative' : 'positive'} font-heading" style="font-weight:600;">$${estBal.toFixed(2)}</td>
                <td><button class="action-btn small-btn danger-btn delete-list-tx-btn" data-key="${t.monthKey}" data-id="${t.id}">Delete</button></td>
            </tr>`;
    });

    document.getElementById('cc-filter-summary').textContent =
`${txList.length} filtered | Charges $${filteredCharges.toFixed(2)} | Payments $${filteredPayments.toFixed(2)} | Filtered balance $${filteredBalance.toFixed(2)}`;

    if (txList.length === 0) {
        container.innerHTML = '<p class="muted-text" style="text-align:center; padding:2rem;">No card transactions match these filters.</p>';
        return;
    }

    container.innerHTML = `
        <table class="data-table">
            <thead><tr><th>Date</th><th>Merchant</th><th>Description</th><th>Owner</th><th>Trip</th><th>Amount</th><th>Filtered Running Balance</th><th>Est. Balance</th><th>Actions</th></tr></thead>
            <tbody>${rowsHtml}</tbody>
        </table>`;

    container.querySelectorAll('.delete-list-tx-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            e.stopPropagation();
            const key = e.target.dataset.key;
            const id = e.target.dataset.id;
            const list = state.cardCalendars[cardId][key] || [];
            const idx = list.findIndex(tx => tx.id === id);
            if (idx > -1) {
                const removed = deleteCardTransactionWithRecurringChoice(cardId, key, id);
                if (!removed) return;
                adjustCardCurrentBalance(cardId, removed.amount, -1);
                saveDatabase();
                renderCardDashboard(cardId);
                logSystem(`Deleted card transaction: ${removed.description} ($${Math.abs(removed.amount).toFixed(2)})`);
            }
        });
    });
    container.querySelectorAll('.editable-row').forEach(row => {
        row.addEventListener('dblclick', () => openEditTransactionModal(row.dataset.id, row.dataset.date));
    });
}
function openEditLoanModal(loanId) {
    const dialog = document.getElementById('loan-dialog');
    const loan = state.loans.find(l => l.id === loanId);
    if (!loan) return;
    
    document.getElementById('loan-modal-title').textContent = "Edit Credit Card / Loan Details";
    document.getElementById('loan-action').value = 'edit';
    document.getElementById('loan-edit-id').value = loanId;
    
    document.getElementById('loan-name-field').value = loan.name;
    document.getElementById('loan-type-field').value = loan.type || 'loan';
    document.getElementById('loan-start-bal').value = loan.startBal;
    document.getElementById('loan-current-bal').value = loan.currentBal;
    document.getElementById('loan-interest-rate').value = loan.interestRate || 0;
    document.getElementById('loan-due-day').value = loan.dueDay || 15;
    document.getElementById('loan-statement-day').value = loan.statementDay || 1;
    document.getElementById('loan-monthly-min').value = loan.monthlyMin;
    document.getElementById('loan-is-charge-card').checked = !!loan.isChargeCard;
    document.getElementById('loan-limit-field').value = loan.isChargeCard ? '' : (loan.limit || 5000);
    document.getElementById('loan-payment-strategy').value = loan.paymentStrategy || 'none';
    document.getElementById('loan-payment-source').value = loan.paymentSource || 'personal';
    document.getElementById('loan-first-payment-date').value = loan.paymentStrategyStartDate || '';
    document.getElementById('loan-payment-end-date').value = loan.paymentEndDate || '';
    document.getElementById('loan-splitter-cycle').value = loan.splitterCycleOverride || (Number(loan.dueDay) <= 14 ? '1st' : '15th');
    document.getElementById('loan-exempt-splitter').checked = !!loan.isExemptFromSplitter;
    
    // Set up promo purchase rate
    const hasPromoPurchase = !!loan.promoActive;
    document.getElementById('loan-purchase-promo-active').checked = hasPromoPurchase;
    document.getElementById('loan-purchase-promo-rate').value = loan.promoRate || 0;
    document.getElementById('loan-purchase-promo-exp').value = loan.promoExpDate || '';
    document.getElementById('loan-purchase-promo-fields').classList.toggle('hidden', !hasPromoPurchase);
    
    // Set up promos list
    tempEditingPromos = JSON.parse(JSON.stringify(loan.promos || []));
    tempEditingPaymentPlans = (loan.paymentPlans || []).map(normalizePaymentPlan);
    resetExistingPlanEditor();
    renderEditingPaymentPlans();
    
    // Toggle promo, limit, and transfer sections based on type
    const isCredit = (loan.type === 'credit');
    document.getElementById('loan-purchase-promo-section').classList.toggle('hidden', !isCredit);
    document.getElementById('loan-payment-plans-section').classList.toggle('hidden', !isCredit);
    document.getElementById('loan-charge-card-group').classList.toggle('hidden', !isCredit);
    document.getElementById('loan-limit-group').classList.toggle('hidden', !isCredit || !!loan.isChargeCard);
    document.getElementById('loan-xfer-section').classList.toggle('hidden', !isCredit);
    document.getElementById('loan-payment-strategy-group').classList.toggle('hidden', !isCredit);
    renderBalanceTransfers(loan);
    document.getElementById('xfer-mode').value = 'new';
    updateBalanceTransferModeFields();
    
    // Populate balance transfer source select dropdown (excluding self)
    const xferSelect = document.getElementById('xfer-source');
    xferSelect.innerHTML = '';
    state.loans.filter(l => l.id !== loanId).forEach(other => {
        const opt = document.createElement('option');
        opt.value = other.id;
        opt.textContent = `${other.name} (Bal: $${other.currentBal.toFixed(2)})`;
        xferSelect.appendChild(opt);
    });

    // Populate mortgage fields
    const isMortgage = !!loan.isMortgage;
    document.getElementById('loan-is-mortgage').checked = isMortgage;
    document.getElementById('loan-mortgage-escrow').value = loan.escrowAmount || 0;
    document.getElementById('loan-mortgage-pi').value = loan.piAmount || 0;
    document.getElementById('loan-mortgage-extra').value = loan.extraPayment || 0;
    document.getElementById('loan-mortgage-section').classList.toggle('hidden', isCredit);
    document.getElementById('loan-mortgage-fields').classList.toggle('hidden', !isMortgage);
    
    dialog.showModal();
}

function renderEditingPromos() {
    const list = document.getElementById('loan-promos-list');
    list.innerHTML = '';
    
    tempEditingPromos.forEach(promo => {
        const item = document.createElement('div');
        item.style.display = 'flex';
        item.style.justifyContent = 'space-between';
        item.style.alignItems = 'center';
        item.style.background = 'rgba(255,255,255,0.03)';
        item.style.padding = '0.3rem 0.6rem';
        item.style.borderRadius = '4px';
        item.style.fontSize = '0.85rem';
        
        let desc = `$${promo.amount.toFixed(2)} @ ${promo.rate}% (Exp: ${promo.expDate})`;
        if (promo.isXfer) {
            const fromLoan = state.loans.find(l => l.id === promo.xferFromId);
            const name = fromLoan ? fromLoan.name : promo.xferFromId;
            desc += ` [Xfer from ${name}]`;
        }
        
        item.innerHTML = `
            <span>${desc}</span>
            <button type="button" class="action-btn small-btn danger-btn delete-promo-row-btn" data-id="${promo.id}" style="padding: 2px 6px; font-size: 0.75rem;">&times;</button>
        `;
        
        item.querySelector('.delete-promo-row-btn').addEventListener('click', (e) => {
            const pId = e.target.dataset.id;
            tempEditingPromos = tempEditingPromos.filter(p => p.id !== pId);
            });
        
        list.appendChild(item);
    });
}

function populatePromoXferSelect() {
    const select = document.getElementById('promo-xfer-from');
    if (!select) return;
    select.innerHTML = '';
    
    state.loans.forEach(loan => {
        const opt = document.createElement('option');
        opt.value = loan.id;
        opt.textContent = loan.name;
        select.appendChild(opt);
    });
}


// --- BILL TRACKER TAB & SYNCHRONIZATION ---

function renderBillTrackerTab() {
    const tbody = document.getElementById('billtracker-table-body');
    if (!tbody) return;
    tbody.innerHTML = '';
    
    const settings = state.billTrackerSettings || [];
    settings.forEach(bill => {
        const sourceName = bill.source === 'jointChecking' ? 'Joint Checking' : 
                           bill.source === 'personalChecking' ? 'Personal Checking' : 
                           (state.loans.find(card => card.id === bill.source)?.name || 'Credit Card');
        
        const autoPayText = bill.autopay ? 'Yes' : 'No';
        
        let recurDesc = 'No';
        if (bill.recurring) {
            const freqLabels = { weekly: 'Weekly', biweekly: 'Every 2 weeks', monthly: 'Monthly', quarterly: 'Every 3 months', annually: 'Annually' };
            recurDesc = `Yes (${freqLabels[bill.frequency] || bill.frequency}${bill.startMonth ? ' starting ' + bill.startMonth : ''})`;
        }
        
        let paymentDateText = '';
        if (bill.dateType === 'dayOfWeek') {
            const weekDays = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
            paymentDateText = `${weekDays[bill.weekday]}<br><span class="muted-text">From ${bill.anchorDate}</span>`;
        } else {
            paymentDateText = `Day ${bill.paymentDate}`;
        }
        
        const closingDateText = (bill.hasClosing && bill.closingDate) ? `Day ${bill.closingDate}` : 'None';
        const ownershipBadge = `<span class="card-icon ${bill.ownership === 'joint' ? 'success' : 'info'}" style="font-size:0.75rem; padding: 2px 6px; display: inline-block; margin-top: 0.25rem;">${bill.ownership === 'joint' ? 'Joint' : 'Personal'}</span>`;
        
        const row = document.createElement('tr');
        row.innerHTML = `
            <td><strong>${escapeHTML(bill.name)}</strong></td>
            <td>${bill.category}<br>${ownershipBadge}</td>
            <td class="negative font-heading" style="font-weight:600;">$${parseFloat(bill.estimate || 0).toFixed(2)}</td>
            <td>${paymentDateText}</td>
            <td>${closingDateText}</td>
            <td>${autoPayText}</td>
            <td>${sourceName}</td>
            <td>${recurDesc}</td>
            <td class="table-actions-cell" style="display:flex; gap:0.4rem; justify-content:flex-end;">
                <button class="action-btn small-btn outline-btn edit-bill-setting-btn" data-id="${bill.id}">Edit</button>
                <button class="action-btn small-btn danger-btn delete-bill-setting-btn" data-id="${bill.id}">Delete</button>
            </td>
        `;
        
        row.querySelector('.edit-bill-setting-btn').addEventListener('click', (e) => {
            openEditBillSettingModal(e.target.dataset.id);
        });
        
        row.querySelector('.delete-bill-setting-btn').addEventListener('click', (e) => {
            const id = e.target.dataset.id;
            const setting = state.billTrackerSettings.find(b => b.id === id);
            if (!setting) return;
            if (confirm(`Delete recurring bill setting for "${setting.name}"?\n\nThis will remove the bill splitter entry and any future planned payments/charges.\n\nAll historical payments/charges that occurred in the past will remain intact for your records.`)) {
                state.billTrackerSettings = state.billTrackerSettings.filter(b => b.id !== id);
                syncBillTrackerBillsToAllMonths();
                saveDatabase();
                renderApp();
                logSystem(`Deleted bill setting: ${setting.name}`);
            }
        });
        
        tbody.appendChild(row);
    });
    
    if (settings.length === 0) {
        tbody.innerHTML = `<tr><td colspan="9" class="muted-text" style="text-align:center;">No bill settings defined. Click "+ Add Bill Setting" to add one.</td></tr>`;
    }
}

function openEditBillSettingModal(id) {
    populateCCDropdowns();
    const form = document.getElementById('bill-settings-form');
    if (!form) return;
    form.reset();
    
    const recurringFields = document.getElementById('bill-settings-recurring-fields');
    recurringFields.classList.add('hidden');
    
    const paymentDateGroup = document.getElementById('bill-settings-payment-date-group');
    const weekdayGroup = document.getElementById('bill-settings-weekday-group');
    const anchorDateGroup = document.getElementById('bill-settings-anchor-date-group');
    const closingDateGroup = document.getElementById('bill-settings-closing-date-group');
    
    paymentDateGroup.classList.remove('hidden');
    weekdayGroup.classList.add('hidden');
    anchorDateGroup.classList.add('hidden');
    closingDateGroup.classList.remove('hidden');
    
    document.getElementById('bill-settings-payment-date').required = true;
    document.getElementById('bill-settings-weekday').required = false;
    document.getElementById('bill-settings-anchor-date').required = false;
    document.getElementById('bill-settings-closing-date').required = true;
    
    if (!id) {
        document.getElementById('bill-settings-modal-title').textContent = "Add Bill Setting";
        document.getElementById('bill-settings-action').value = 'add';
        document.getElementById('bill-settings-id').value = '';
        document.getElementById('bill-settings-autopay').checked = true;
        document.getElementById('bill-settings-recurring').checked = true;
        document.getElementById('bill-settings-has-closing').checked = true;
        document.getElementById('bill-settings-date-type').value = 'dayOfMonth';
        document.getElementById('bill-settings-ownership').value = 'joint';
        document.getElementById('bill-settings-cycle').value = '1st';
        document.getElementById('bill-settings-first-payment').value = '';
        document.getElementById('bill-settings-frequency').value = 'monthly';
        recurringFields.classList.remove('hidden');
    } else {
        const setting = state.billTrackerSettings.find(b => b.id === id);
        if (!setting) return;
        
        document.getElementById('bill-settings-modal-title').textContent = "Edit Bill Setting";
        document.getElementById('bill-settings-action').value = 'edit';
        document.getElementById('bill-settings-id').value = setting.id;
        
        document.getElementById('bill-settings-name').value = setting.name;
        document.getElementById('bill-settings-category').value = setting.category;
        document.getElementById('bill-settings-ownership').value = setting.ownership || 'joint';
        document.getElementById('bill-settings-estimate').value = setting.estimate;
        document.getElementById('bill-settings-date-type').value = setting.dateType || 'dayOfMonth';
        
        if (setting.dateType === 'dayOfWeek') {
            paymentDateGroup.classList.add('hidden');
            weekdayGroup.classList.remove('hidden');
            anchorDateGroup.classList.remove('hidden');
            
            document.getElementById('bill-settings-payment-date').required = false;
            document.getElementById('bill-settings-weekday').required = true;
            document.getElementById('bill-settings-anchor-date').required = true;
            
            document.getElementById('bill-settings-weekday').value = setting.weekday ?? '1';
            document.getElementById('bill-settings-anchor-date').value = setting.anchorDate || '';
        } else {
            document.getElementById('bill-settings-payment-date').value = setting.paymentDate || '1';
        }
        
        const hasClosing = setting.hasClosing !== false && setting.closingDate;
        document.getElementById('bill-settings-has-closing').checked = hasClosing;
        if (hasClosing) {
            document.getElementById('bill-settings-closing-date').value = setting.closingDate;
        } else {
            closingDateGroup.classList.add('hidden');
            document.getElementById('bill-settings-closing-date').required = false;
        }
        
        document.getElementById('bill-settings-autopay').checked = !!setting.autopay;
        document.getElementById('bill-settings-recurring').checked = !!setting.recurring;
        document.getElementById('bill-settings-source').value = setting.source;
        document.getElementById('bill-settings-cycle').value = setting.cycleAllocation || '1st';
        document.getElementById('bill-settings-first-payment').value = setting.firstPaymentDate || '';
        
        if (setting.recurring) {
            recurringFields.classList.remove('hidden');
            document.getElementById('bill-settings-frequency').value = setting.frequency || 'monthly';
            document.getElementById('bill-settings-start-month').value = setting.startMonth || 'Jan';
        }
    }
    
    document.getElementById('bill-settings-dialog').showModal();
}

function setupBillTrackerListeners() {
    const form = document.getElementById('bill-settings-form');
    if (form) {
        form.addEventListener('submit', (e) => {
            e.preventDefault();
            const action = document.getElementById('bill-settings-action').value;
            const id = document.getElementById('bill-settings-id').value;
            
            const name = document.getElementById('bill-settings-name').value.trim();
            const category = document.getElementById('bill-settings-category').value;
            const ownership = document.getElementById('bill-settings-ownership').value;
            const estimate = parseFloat(document.getElementById('bill-settings-estimate').value) || 0;
            const dateType = document.getElementById('bill-settings-date-type').value;
            
            let paymentDate = 1;
            let weekday = 1;
            let anchorDate = '';
            
            if (dateType === 'dayOfWeek') {
                weekday = parseInt(document.getElementById('bill-settings-weekday').value, 10);
                anchorDate = document.getElementById('bill-settings-anchor-date').value;
            } else {
                paymentDate = parseInt(document.getElementById('bill-settings-payment-date').value, 10) || 1;
            }
            
            const hasClosing = document.getElementById('bill-settings-has-closing').checked;
            let closingDate = null;
            if (hasClosing) {
                closingDate = parseInt(document.getElementById('bill-settings-closing-date').value, 10) || 1;
            }
            
            const autopay = document.getElementById('bill-settings-autopay').checked;
            const recurring = document.getElementById('bill-settings-recurring').checked;
            const source = document.getElementById('bill-settings-source').value;
            const cycleAllocation = document.getElementById('bill-settings-cycle').value;
            const firstPaymentDate = document.getElementById('bill-settings-first-payment').value;
            
            let frequency = 'monthly';
            let startMonth = 'Jan';
            if (recurring) {
                frequency = document.getElementById('bill-settings-frequency').value;
                startMonth = document.getElementById('bill-settings-start-month').value;
            }
            
            if (action === 'add') {
                const newSetting = {
                    id: 'bs-' + Math.random().toString(36).substr(2, 9),
                    name,
                    category,
                    ownership,
                    estimate,
                    dateType,
                    paymentDate,
                    weekday,
                    anchorDate,
                    hasClosing,
                    closingDate,
                    autopay,
                    recurring,
                    source,
                    frequency,
                    startMonth,
                    cycleAllocation,
                    firstPaymentDate
                };
                state.billTrackerSettings.push(newSetting);
            } else {
                const setting = state.billTrackerSettings.find(b => b.id === id);
                if (setting) {
                    setting.name = name;
                    setting.category = category;
                    setting.ownership = ownership;
                    setting.estimate = estimate;
                    setting.dateType = dateType;
                    setting.paymentDate = paymentDate;
                    setting.weekday = weekday;
                    setting.anchorDate = anchorDate;
                    setting.hasClosing = hasClosing;
                    setting.closingDate = closingDate;
                    setting.autopay = autopay;
                    setting.recurring = recurring;
                    setting.source = source;
                    setting.frequency = frequency;
                    setting.startMonth = startMonth;
                    setting.cycleAllocation = cycleAllocation;
                    setting.firstPaymentDate = firstPaymentDate;
                }
            }
            
            syncBillTrackerBillsToAllMonths();
            saveDatabase();
            renderApp();
            document.getElementById('bill-settings-dialog').close();
            logSuccess(`Saved bill setting for "${name}".`);
        });
    }
    
    const btnAdd = document.getElementById('btn-add-bill-tracker-setting');
    if (btnAdd) {
        btnAdd.addEventListener('click', () => {
            openEditBillSettingModal();
        });
    }
    
    const btnCancel = document.getElementById('btn-cancel-bill-settings');
    if (btnCancel) {
        btnCancel.addEventListener('click', () => {
            document.getElementById('bill-settings-dialog').close();
        });
    }
    
    const btnCloseWarning = document.getElementById('btn-close-delete-warning');
    if (btnCloseWarning) {
        btnCloseWarning.addEventListener('click', () => {
            document.getElementById('delete-billtracker-warning-dialog').close();
        });
    }
    
    const recurringCheckbox = document.getElementById('bill-settings-recurring');
    if (recurringCheckbox) {
        recurringCheckbox.addEventListener('change', (e) => {
            document.getElementById('bill-settings-recurring-fields').classList.toggle('hidden', !e.target.checked);
        });
    }
    
    const dateTypeSelect = document.getElementById('bill-settings-date-type');
    if (dateTypeSelect) {
        dateTypeSelect.addEventListener('change', (e) => {
            const isWeek = e.target.value === 'dayOfWeek';
            document.getElementById('bill-settings-payment-date-group').classList.toggle('hidden', isWeek);
            document.getElementById('bill-settings-weekday-group').classList.toggle('hidden', !isWeek);
            document.getElementById('bill-settings-anchor-date-group').classList.toggle('hidden', !isWeek);
            
            document.getElementById('bill-settings-payment-date').required = !isWeek;
            document.getElementById('bill-settings-weekday').required = isWeek;
            document.getElementById('bill-settings-anchor-date').required = isWeek;
        });
    }
    
    const hasClosingCheckbox = document.getElementById('bill-settings-has-closing');
    if (hasClosingCheckbox) {
        hasClosingCheckbox.addEventListener('change', (e) => {
            const hasClosing = e.target.checked;
            document.getElementById('bill-settings-closing-date-group').classList.toggle('hidden', !hasClosing);
            document.getElementById('bill-settings-closing-date').required = hasClosing;
        });
    }
}

function syncBillTrackerBillsToAllMonths() {
    const activeSettings = state.billTrackerSettings || [];
    
    Object.keys(state.monthlyBills || {}).forEach(key => {
        const mBills = state.monthlyBills[key];
        if (!mBills) return;
        
        const [y, m] = key.split('-');
        const periodIndex = Number(y) * 12 + MONTH_ORDER.indexOf(m);
        // Use the real calendar date here, not state.currentYear/currentMonth — that's just whichever
        // month the UI happens to be scrolled to. Using it as the "don't touch the past" cutoff meant
        // a newly-created bill setting would silently skip every month up to whatever month you'd last
        // viewed, even the actual current month, if you happened to be looking further ahead when you saved it.
        const today = new Date();
        const currentIndex = today.getFullYear() * 12 + today.getMonth();

        // 1. Delete bills that are no longer in activeSettings (for current and future months only)
        ['cycle1st', 'cycle15th'].forEach(cycleKey => {
            mBills[cycleKey].bills = (mBills[cycleKey].bills || []).filter(b => {
                if (b.billTrackerSettingId) {
                    const exists = activeSettings.some(s => s.id === b.billTrackerSettingId);
                    if (!exists) {
                        if (periodIndex >= currentIndex) {
                            removeBillLedgerEntries(b.id, Number(y), m, b, true);
                            return false;
                        }
                    }
                }
                return true;
            });
        });
        
        // 2. Add or update active settings (for current and future months only)
        if (periodIndex >= currentIndex) {
            activeSettings.forEach(setting => {
                const billId = `bill-settings-${setting.id}`;

                // First Payment Date gate: don't materialize the bill in months before the first
                // payment, and within the first month only if the payment day falls on/after it.
                if (setting.firstPaymentDate) {
                    const fp = new Date(setting.firstPaymentDate + 'T00:00:00');
                    if (!Number.isNaN(fp.getTime())) {
                        const fpIndex = fp.getFullYear() * 12 + fp.getMonth();
                        const paymentDay = setting.dateType === 'dayOfWeek' ? 1 : (Number(setting.paymentDate) || 1);
                        const beforeFirstPayment = periodIndex < fpIndex || (periodIndex === fpIndex && paymentDay < fp.getDate());
                        if (beforeFirstPayment) {
                            // Match on billTrackerSettingId, not the exact row id — recurrence
                            // inheritance also creates month-suffixed copies of the synced row.
                            ['cycle1st', 'cycle15th'].forEach(cycleKey => {
                                mBills[cycleKey].bills = mBills[cycleKey].bills.filter(b => {
                                    if (b.billTrackerSettingId !== setting.id) return true;
                                    removeBillLedgerEntries(b.id, Number(y), m, b, true);
                                    return false;
                                });
                            });
                            return;
                        }
                    }
                }

                // Determine cycle Allocation
                let targetCycleKey = 'cycle1st';
                if (setting.frequency === 'weekly' || setting.frequency === 'biweekly') {
                    targetCycleKey = 'cycle1st';
                } else if (setting.dateType === 'dayOfWeek') {
                    const mockBill = {
                        chargeFrequency: setting.frequency || 'monthly',
                        frequencyStartDate: setting.anchorDate,
                        weeklyDay: setting.weekday
                    };
                    const occurrenceDates = getBillOccurrenceDates(mockBill, Number(y), m);
                    if (occurrenceDates.length > 0) {
                        const day = new Date(occurrenceDates[0] + 'T00:00:00').getDate();
                        targetCycleKey = day <= 14 ? 'cycle1st' : 'cycle15th';
                    } else {
                        targetCycleKey = 'cycle1st';
                    }
                } else {
                    targetCycleKey = setting.paymentDate <= 14 ? 'cycle1st' : 'cycle15th';
                }
                
                let bill = mBills.cycle1st.bills.find(b => b.id === billId) || mBills.cycle15th.bills.find(b => b.id === billId);
                const budgetAmount = parseFloat(setting.estimate || 0);
                
                const freqMapping = { 
                    weekly: 'weekly', 
                    biweekly: 'biweekly', 
                    monthly: setting.dateType === 'dayOfWeek' ? 'fourweekly' : 'monthly', 
                    quarterly: 'quarterly', 
                    annually: 'annual' 
                };
                const mappedFreq = freqMapping[setting.frequency] || 'monthly';
                
                // Prefer the user's explicit Transfer Cycle choice (set in the Bill Settings form);
                // fall back to the old auto-derived rule (weekly/biweekly bills split across both
                // cycles, everything else follows its due-day cycle) for settings created before that
                // field existed.
                const cycleAllocationVal = setting.cycleAllocation || ((setting.frequency === 'weekly' || setting.frequency === 'biweekly' || mappedFreq === 'fourweekly') ? 'both' : (targetCycleKey === 'cycle1st' ? '1st' : '15th'));
                
                if (bill) {
                    bill.account = setting.name;
                    bill.category = 'bill';
                    bill.billTrackerCategory = setting.category || '';
                    bill.dueDay = setting.dateType === 'dayOfWeek' ? 1 : (Number(setting.paymentDate) || 1);
                    bill.paymentSource = setting.source;
                    bill.ownership = setting.ownership || 'joint';
                    bill.entryType = setting.autopay ? 'actual' : 'calculation';
                    bill.isRecurring = !!setting.recurring;
                    bill.chargeFrequency = mappedFreq;
                    bill.recurringStartMonth = setting.startMonth || 'Jan';
                    bill.frequencyAmount = budgetAmount;
                    
                    if (setting.dateType === 'dayOfWeek') {
                        bill.frequencyStartDate = setting.anchorDate;
                        bill.weeklyDay = setting.weekday;
                    } else {
                        bill.frequencyStartDate = '';
                        bill.weeklyDay = null;
                    }
                    
                    if (bill.samePaymentAmount) {
                        bill.occurrencePaymentAmount = budgetAmount;
                    }
                    
                    const currentCycleKey = mBills.cycle1st.bills.includes(bill) ? 'cycle1st' : 'cycle15th';
                    if (currentCycleKey !== targetCycleKey) {
                        mBills[currentCycleKey].bills = mBills[currentCycleKey].bills.filter(b => b.id !== billId);
                        mBills[targetCycleKey].bills.push(bill);
                    }
                    bill.cycleAllocation = cycleAllocationVal;
                    
                    const recalculated = recalculateBillBudgetForPeriod(bill, Number(y), m);
                    Object.assign(bill, recalculated);
                    syncBillLedgerEntry(bill, Number(y), m);
                } else {
                    const newBill = {
                        id: billId,
                        account: setting.name,
                        category: 'bill',
                        billTrackerCategory: setting.category || '',
                        amount: -Math.abs(budgetAmount),
                        budgetAmount: budgetAmount,
                        frequencyAmount: budgetAmount,
                        paymentAmount: budgetAmount,
                        occurrencePaymentAmount: budgetAmount,
                        dueDay: setting.dateType === 'dayOfWeek' ? 1 : (Number(setting.paymentDate) || 1),
                        paymentSource: setting.source,
                        ownership: setting.ownership || 'joint',
                        cycleAllocation: cycleAllocationVal,
                        isRecurring: !!setting.recurring,
                        samePaymentAmount: true,
                        billTrackerSettingId: setting.id,
                        entryType: setting.autopay ? 'actual' : 'calculation',
                        chargeFrequency: mappedFreq,
                        recurringStartMonth: setting.startMonth || 'Jan'
                    };
                    
                    if (setting.dateType === 'dayOfWeek') {
                        newBill.frequencyStartDate = setting.anchorDate;
                        newBill.weeklyDay = setting.weekday;
                    }
                    
                    mBills[targetCycleKey].bills.push(newBill);
                    
                    const recalculated = recalculateBillBudgetForPeriod(newBill, Number(y), m);
                    Object.assign(newBill, recalculated);
                    syncBillLedgerEntry(newBill, Number(y), m);
                }
            });
        }
        
        recalculateBillCycleTotals(mBills);
    });
}

// --- TRIGGER INITIALIZATION ---
window.addEventListener('DOMContentLoaded', init);
