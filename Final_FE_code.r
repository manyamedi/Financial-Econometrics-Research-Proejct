# ETF portfolio risk: static copulas and a DCC Gaussian copula
# 1. SETUP

# Packages used in the analysis
packages <- c("rugarch", "rmgarch", "copula", "xtable", "xts")
missing_packages <- packages[
  !vapply(packages, requireNamespace, logical(1), quietly = TRUE)
]
if (length(missing_packages)) {
  stop("Install these packages first: ", paste(missing_packages, collapse = ", "))
}
library(rugarch)
library(rmgarch)
library(copula)

# Input CSVs and where the tables, plots and saved objects go
folder <- "/Users/manya/Desktop/Financial/Data/"
output_folder <- file.path(folder, "clean_final_results")
dir.create(output_folder, recursive = TRUE, showWarnings = FALSE)

# Sample, simulation settings and cut-offs used throughout
tickers <- c("VAS", "VGS", "GOLD", "VAF")
n_assets <- length(tickers)
seed <- 42L
M <- 100000L
tail_p <- 0.10
confidence_levels <- c(0.90, 0.95, 0.99)
allocation_confidence <- 0.99
weight_step <- 0.05
exceedance_probs <- c(0.05, 0.10, 0.15, 0.20)
primary_q <- 0.10
min_joint <- 20L
bootstrap_reps <- 499L
block_lengths <- c(10L, 20L)
seed_set <- c(1L, 123L, 777L, 2024L, 2026L)
tail_fractions <- c(0.05, 0.10, 0.15)
set.seed(seed)

# 2. FUNCTIONS

# Save the R tables as LaTeX files
save_latex <- function(data, filename, caption, label, digits = 4) {
  table <- xtable::xtable(data, caption = caption, label = label, digits = digits)
  print(table, type = "latex", file = file.path(output_folder, filename),
        include.rownames = FALSE, booktabs = TRUE, caption.placement = "top",
        table.placement = "htbp", comment = FALSE)
}

# Fit a GPD to the excesses beyond a chosen tail threshold
fit_gpd <- function(y) {
  if (length(y) < 30 || any(!is.finite(y)) || any(y <= 0)) {
    stop("A GPD fit needs at least 30 finite, positive excesses.")
  }
  nll <- function(par) {
    beta <- exp(par[1])
    xi <- par[2]
    if (!is.finite(beta) || beta <= 0 || !is.finite(xi)) return(1e10)
    a <- 1 + xi * y / beta
    if (any(!is.finite(a)) || any(a <= 0)) return(1e10)
    if (abs(xi) < 1e-6) return(length(y) * log(beta) + sum(y) / beta)
    length(y) * log(beta) + (1 + 1 / xi) * sum(log(a))
  }
  fit <- optim(c(log(mean(y)), 0.1), nll, control = list(maxit = 2000))
  if (fit$convergence != 0 || !is.finite(fit$value) || fit$value >= 1e10) {
    stop("The GPD optimizer did not produce a valid converged fit.")
  }
  g <- c(beta = exp(fit$par[1]), xi = fit$par[2])
  if (any(1 + g["xi"] * y / g["beta"] <= 0)) stop("GPD support check failed.")
  if (g["xi"] <= -0.5) warning("GPD shape <= -0.5: ordinary likelihood inference is non-regular.")
  if (g["xi"] >= 0.5) warning("GPD shape >= 0.5: this fitted tail has no finite second moment.")
  g
}

# GPD survival probability, used for the fitted tails
gpd_tailprob <- function(y, g) {
  if (any(!is.finite(y)) || any(y < 0)) stop("Invalid GPD excesses.")
  beta <- unname(g["beta"])
  xi <- unname(g["xi"])
  if (abs(xi) < 1e-6) return(exp(-y / beta))
  probability <- numeric(length(y))
  inside <- 1 + xi * y / beta > 0
  probability[inside] <- exp(-log1p(xi * y[inside] / beta) / xi)
  probability
}

# Reverse the GPD survival probability to get an excess
gpd_inverse <- function(p, g) {
  if (any(!is.finite(p)) || any(p <= 0 | p > 1)) {
    stop("GPD survival probabilities must be in (0, 1].")
  }
  beta <- unname(g["beta"])
  xi <- unname(g["xi"])
  if (abs(xi) < 1e-6) return(-beta * log(p))
  beta / xi * expm1(-xi * log(p))
}

# Use empirical values in the middle and separate GPDs in both tails
fit_margin <- function(z, tail_probability) {
  if (any(!is.finite(z)) || tail_probability <= 0 || tail_probability >= 0.5) {
    stop("Invalid residuals or tail probability.")
  }
  uL <- unname(quantile(z, tail_probability))
  uR <- unname(quantile(z, 1 - tail_probability))
  if (uL >= uR) stop("The marginal thresholds must be distinct.")
  lower_excess <- uL - z[z < uL]
  upper_excess <- z[z > uR] - uR
  gL <- fit_gpd(lower_excess)
  gR <- fit_gpd(upper_excess)
  sorted_z <- sort(z)
  points <- aggregate(seq(0, 1, length.out = length(z)),
                      by = list(z = sorted_z), FUN = mean)
  names(points)[2] <- "p"
  points <- points[order(points$z), ]
  keep <- points$z > uL & points$z < uR &
    points$p > tail_probability & points$p < 1 - tail_probability
  list(uL = uL, uR = uR, tail_p = tail_probability, gL = gL, gR = gR,
       lower_n = length(lower_excess), upper_n = length(upper_excess),
       mid_z = c(uL, points$z[keep], uR),
       mid_p = c(tail_probability, points$p[keep], 1 - tail_probability))
}

# Convert standardised residuals to probabilities using an EVT margin
F_cdf <- function(x, m) {
  if (any(!is.finite(x))) stop("The marginal CDF requires finite residuals.")
  u <- approx(m$mid_z, m$mid_p, xout = x, rule = 2)$y
  lo <- x < m$uL
  hi <- x > m$uR
  u[lo] <- m$tail_p * gpd_tailprob(m$uL - x[lo], m$gL)
  u[hi] <- 1 - m$tail_p * gpd_tailprob(x[hi] - m$uR, m$gR)
  u
}

# Convert probabilities back into standardised residuals
F_inv <- function(u, m) {
  if (any(!is.finite(u)) || any(u <= 0 | u >= 1)) {
    stop("Marginal probabilities must be strictly inside (0, 1).")
  }
  x <- approx(m$mid_p, m$mid_z, xout = u, rule = 2)$y
  lo <- u < m$tail_p
  hi <- u > 1 - m$tail_p
  x[lo] <- m$uL - gpd_inverse(u[lo] / m$tail_p, m$gL)
  x[hi] <- m$uR + gpd_inverse((1 - u[hi]) / m$tail_p, m$gR)
  x
}

# Check that each CDF and inverse return the starting probabilities
check_margins <- function(margins, probabilities) {
  do.call(rbind, lapply(names(margins), function(tk) {
    quantiles <- F_inv(probabilities, margins[[tk]])
    error <- max(abs(F_cdf(quantiles, margins[[tk]]) - probabilities))
    increasing <- all(diff(quantiles) > 0)
    if (any(!is.finite(quantiles)) || !increasing || !is.finite(error) || error > 1e-7) {
      stop(tk, ": marginal CDF/inverse check failed.")
    }
    data.frame(ETF = tk, Maximum_inverse_error = error, Increasing_quantiles = increasing)
  }))
}

# Put the lower- and upper-tail GPD estimates into a table
margin_table <- function(margins) {
  do.call(rbind, lapply(names(margins), function(tk) {
    m <- margins[[tk]]
    data.frame(ETF = tk, Tail = c("Lower", "Upper"),
               Threshold = c(m$uL, m$uR), Exceedances = c(m$lower_n, m$upper_n),
               Shape = c(unname(m$gL["xi"]), unname(m$gR["xi"])),
               Scale = c(unname(m$gL["beta"]), unname(m$gR["beta"])))
  }))
}

# Draw dependent uniforms from each fitted copula, including the DCC forecast
simulate_uniforms <- function(static_fits, R_next, M, seed) {
  set.seed(seed)
  draws <- lapply(static_fits, function(fit) rCopula(M, fit@copula))

  # chol() is upper triangular, so these draws have correlation R_next.
  gaussian <- matrix(rnorm(M * ncol(R_next)), M, ncol(R_next)) %*% chol(R_next)
  draws$DCC_Gaussian <- pnorm(gaussian)
  for (model in names(draws)) {
    u <- draws[[model]]
    if (any(!is.finite(u)) || any(u < 0 | u > 1)) stop(model, ": invalid uniforms.")
    u <- pmin(pmax(u, 1e-12), 1 - 1e-12)
    colnames(u) <- colnames(R_next)
    draws[[model]] <- u
  }
  draws
}

# Apply the fitted EVT inverse margins to the copula draws
uniforms_to_shocks <- function(u, margins) {
  shocks <- sapply(names(margins), function(tk) F_inv(u[, tk], margins[[tk]]))
  colnames(shocks) <- names(margins)
  if (any(!is.finite(shocks))) stop("Non-finite simulated EVT shocks.")
  shocks
}

# Add the one-day volatility and mean forecasts; convert to simple returns
shocks_to_returns <- function(shocks, mu, sigma_next) {
  assets <- colnames(shocks)
  means <- mu[assets]
  volatility <- sigma_next[assets]
  if (any(!is.finite(c(means, volatility))) || any(volatility <= 0)) {
    stop("Invalid marginal forecasts.")
  }
  log_returns <- sweep(sweep(shocks, 2, volatility, "*"), 2, means, "+")
  simple_returns <- 100 * expm1(log_returns / 100)
  if (any(!is.finite(simple_returns))) stop("Non-finite simulated returns.")
  simple_returns
}

# Calculate loss VaR and CVaR at a given confidence level
var_cvar <- function(portfolio_returns, confidence) {
  loss <- -as.numeric(portfolio_returns)
  if (length(confidence) != 1 || !is.finite(confidence) || confidence <= 0 || confidence >= 1) {
    stop("Confidence must be between zero and one.")
  }
  if (!length(loss) || any(!is.finite(loss))) stop("Invalid portfolio returns.")
  VaR <- unname(quantile(loss, confidence, type = 1))
  CVaR <- VaR + mean(pmax(loss - VaR, 0)) / (1 - confidence)
  c(VaR = VaR, CVaR = CVaR)
}

# Equal-weight portfolio risk for each copula and confidence level
summarise_risk <- function(return_draws, confidence_levels) {
  do.call(rbind, lapply(names(return_draws), function(model) {
    portfolio <- as.numeric(return_draws[[model]][, tickers, drop = FALSE] %*% w_equal)
    do.call(rbind, lapply(confidence_levels, function(confidence) {
      risk <- var_cvar(portfolio, confidence)
      data.frame(Model = model, Confidence = confidence,
                 VaR = unname(risk["VaR"]), CVaR = unname(risk["CVaR"]))
    }))
  }))
}

# Search the weight grid in batches and retain the lowest-CVaR portfolio
minimum_cvar <- function(asset_returns, weights, confidence, batch_size = 20L) {
  asset_returns <- as.matrix(asset_returns[, colnames(weights), drop = FALSE])
  if (any(!is.finite(asset_returns))) stop("Invalid asset return scenarios.")
  portfolio_var <- portfolio_cvar <- numeric(nrow(weights))
  for (first in seq.int(1L, nrow(weights), by = batch_size)) {
    index <- first:min(first + batch_size - 1L, nrow(weights))
    portfolios <- asset_returns %*% t(weights[index, , drop = FALSE])
    risks <- vapply(seq_along(index), function(j) var_cvar(portfolios[, j], confidence),
                    c(VaR = 0, CVaR = 0))
    portfolio_var[index] <- risks["VaR", ]
    portfolio_cvar[index] <- risks["CVaR", ]
  }
  best <- which.min(portfolio_cvar)
  list(weights = weights[best, ], VaR = portfolio_var[best], CVaR = portfolio_cvar[best])
}

# Joint lower- and upper-tail events for every ETF pair
# Correlations are only reported when there are enough joint observations.
exceedance_summary <- function(values, uniforms, probabilities, min_joint) {
  values <- as.matrix(values)
  uniforms <- as.matrix(uniforms)
  stopifnot(identical(dim(values), dim(uniforms)),
            identical(colnames(values), colnames(uniforms)),
            all(is.finite(values)), all(is.finite(uniforms)))
  pairs <- combn(seq_len(ncol(values)), 2)
  rows <- list()
  h <- 1L
  for (k in seq_len(ncol(pairs))) {
    i <- pairs[1, k]
    j <- pairs[2, k]
    for (q in probabilities) {
      for (side in c("Lower", "Upper")) {
        event_i <- if (side == "Lower") uniforms[, i] < q else uniforms[, i] > 1 - q
        event_j <- if (side == "Lower") uniforms[, j] < q else uniforms[, j] > 1 - q
        joint <- event_i & event_j
        n_joint <- sum(joint)
        rho <- NA_real_
        if (n_joint >= min_joint && sd(values[joint, i]) > 0 && sd(values[joint, j]) > 0) {
          rho <- cor(values[joint, i], values[joint, j])
        }
        rows[[h]] <- data.frame(
          Pair = paste(colnames(values)[c(i, j)], collapse = "-"), Tail = side, q = q,
          N = nrow(values), N_i = sum(event_i), N_j = sum(event_j), N_joint = n_joint,
          Correlation = rho, Joint_frequency = mean(joint),
          Conditional_j_given_i = if (sum(event_i)) n_joint / sum(event_i) else NA_real_)
        h <- h + 1L
      }
    }
  }
  do.call(rbind, rows)
}

# Circular block bootstrap for uncertainty in observed tail measures
bootstrap_exceedance <- function(values, uniforms, probabilities, min_joint,
                                 reps, block_length, seed) {
  set.seed(seed)
  values <- as.matrix(values)
  uniforms <- as.matrix(uniforms)
  observed <- exceedance_summary(values, uniforms, probabilities, min_joint)
  n <- nrow(values)
  correlation_draws <- frequency_draws <- matrix(NA_real_, reps, nrow(observed))
  for (b in seq_len(reps)) {
    starts <- sample.int(n, ceiling(n / block_length), replace = TRUE)
    index <- unlist(lapply(starts, function(start) {
      (start - 1L + 0:(block_length - 1L)) %% n + 1L
    }), use.names = FALSE)[seq_len(n)]
    result <- exceedance_summary(values[index, , drop = FALSE],
                                  uniforms[index, , drop = FALSE], probabilities, min_joint)
    correlation_draws[b, ] <- result$Correlation
    frequency_draws[b, ] <- result$Joint_frequency
  }
  interval <- function(x) {
    valid <- is.finite(x)
    if (sum(valid) < ceiling(0.80 * reps)) return(c(NA_real_, NA_real_))
    unname(quantile(x[valid], c(0.025, 0.975)))
  }
  rho_ci <- t(apply(correlation_draws, 2, interval))
  frequency_ci <- t(apply(frequency_draws, 2, interval))
  rho_ci[!is.finite(observed$Correlation), ] <- NA_real_
  observed$Block_length <- block_length
  observed$Valid_correlation_bootstraps <- colSums(is.finite(correlation_draws))
  observed$Correlation_lower <- rho_ci[, 1]
  observed$Correlation_upper <- rho_ci[, 2]
  observed$Joint_frequency_lower <- frequency_ci[, 1]
  observed$Joint_frequency_upper <- frequency_ci[, 2]
  observed
}

# Longin-Solnik style: condition on either ETF being in its own tail.
# This is different from conditioning on both ETFs being extreme.
ls_exceedance_correlation <- function(values, uniforms, q, min_obs = 20) {
  values <- as.matrix(values)
  uniforms <- as.matrix(uniforms)
  stopifnot(identical(dim(values), dim(uniforms)),
            all(is.finite(values)), all(is.finite(uniforms)))

  pairs <- combn(seq_len(ncol(values)), 2)
  rows <- list()

  for (k in seq_len(ncol(pairs))) {
    i <- pairs[1, k]
    j <- pairs[2, k]

    for (side in c("Lower", "Upper")) {
      if (side == "Lower") {
        event_i <- uniforms[, i] < q
        event_j <- uniforms[, j] < q
      } else {
        event_i <- uniforms[, i] > 1 - q
        event_j <- uniforms[, j] > 1 - q
      }

      rho_i <- rho_j <- NA_real_

      if (sum(event_i) >= min_obs) {
        rho_i <- cor(values[event_i, i], values[event_i, j])
      }

      if (sum(event_j) >= min_obs) {
        rho_j <- cor(values[event_j, i], values[event_j, j])
      }

      rows[[length(rows) + 1]] <- data.frame(
        Pair = paste(colnames(values)[c(i, j)], collapse = "-"),
        Tail = side,
        q = q,
        N_i = sum(event_i),
        N_j = sum(event_j),
        Corr_given_i_extreme = rho_i,
        Corr_given_j_extreme = rho_j,
        Average_exceedance_correlation =
          mean(c(rho_i, rho_j), na.rm = TRUE)
      )
    }
  }

  do.call(rbind, rows)
}

# Finite-threshold lower- and upper-tail co-exceedance rates
empirical_tail_dependence <- function(uniforms, u = c(0.05, 0.10)) {
  uniforms <- as.matrix(uniforms)
  stopifnot(all(is.finite(uniforms)))
  pairs <- combn(seq_len(ncol(uniforms)), 2)
  rows <- list()

  for (k in seq_len(ncol(pairs))) {
    i <- pairs[1, k]
    j <- pairs[2, k]

    for (threshold in u) {
      lower_i <- uniforms[, i] < threshold
      lower_j <- uniforms[, j] < threshold
      upper_i <- uniforms[, i] > 1 - threshold
      upper_j <- uniforms[, j] > 1 - threshold

      rows[[length(rows) + 1]] <- data.frame(
        Pair = paste(colnames(uniforms)[c(i, j)], collapse = "-"),
        u = threshold,
        Lambda_L = ifelse(sum(lower_i) > 0,
                          sum(lower_i & lower_j) / sum(lower_i), NA_real_),
        Lambda_U = ifelse(sum(upper_i) > 0,
                          sum(upper_i & upper_j) / sum(upper_i), NA_real_)
      )
    }
  }

  do.call(rbind, rows)
}

# 3. PRICES, RETURNS AND GARCH MODELS

# Read each adjusted-price series and keep a record of missing observations
price_list <- data_audit <- vector("list", n_assets)
for (i in seq_along(tickers)) {
  tk <- tickers[i]
  file <- file.path(folder, paste0(tk, ".AX.csv"))
  if (!file.exists(file)) stop("File not found: ", file)
  df <- read.csv(file, na.strings = c("", "NA", "null", "NULL"), check.names = TRUE)
  if (!all(c("Date", "Adj.Close") %in% names(df))) stop(tk, ": Date and Adj.Close required.")
  date <- as.Date(df$Date)
  price <- suppressWarnings(as.numeric(df$Adj.Close))
  if (anyNA(date) || anyDuplicated(date)) stop(tk, ": invalid or duplicated dates.")
  if (any(price <= 0, na.rm = TRUE) || any(is.infinite(price))) stop(tk, ": invalid prices.")
  valid <- !is.na(price)
  price_list[[i]] <- data.frame(Date = date[valid], Price = price[valid])
  names(price_list[[i]])[2] <- tk
  data_audit[[i]] <- data.frame(ETF = tk, Input_rows = nrow(df),
                               Missing_prices = sum(!valid), Valid_prices = sum(valid))
}

# Work with the dates common to all four ETFs
prices <- Reduce(function(x, y) merge(x, y, by = "Date"), price_list)
prices <- prices[order(prices$Date), ]
rownames(prices) <- NULL
if (nrow(prices) < 500) stop("Fewer than 500 common prices.")
data_audit <- do.call(rbind, data_audit)
data_audit$Common_prices <- nrow(prices)
data_audit$Excluded_by_alignment <- data_audit$Valid_prices - nrow(prices)

# Daily log returns, expressed in percentage points
returns <- as.data.frame(100 * apply(log(as.matrix(prices[, tickers])), 2, diff))
names(returns) <- tickers
return_dates <- prices$Date[-1]
stopifnot(nrow(returns) == length(return_dates), all(is.finite(as.matrix(returns))))
sample_info <- data.frame(Start = min(return_dates), End = max(return_dates), Observations = nrow(returns))

# Descriptive statistics and the Jarque-Bera statistic
skew <- function(x) mean((x - mean(x))^3) / sd(x)^3
kurt <- function(x) mean((x - mean(x))^4) / sd(x)^4
jb <- function(x) length(x) / 6 * (skew(x)^2 + (kurt(x) - 3)^2 / 4)
table1 <- t(sapply(returns, function(x) {
  c(Mean = mean(x), Min = min(x), Max = max(x), Std = sd(x),
    Skew = skew(x), Kurtosis = kurt(x), JB = jb(x))
}))

# Student-t GARCH(1,1) for VAS, VGS and GOLD; GJR-GARCH for VAF
spec_garch11 <- ugarchspec(
  variance.model = list(model = "sGARCH", garchOrder = c(1, 1), variance.targeting = TRUE),
  mean.model = list(armaOrder = c(0, 0), include.mean = TRUE), distribution.model = "std")
spec_gjr <- ugarchspec(
  variance.model = list(model = "gjrGARCH", garchOrder = c(1, 1), variance.targeting = TRUE),
  mean.model = list(armaOrder = c(0, 0), include.mean = TRUE), distribution.model = "std")
univariate_specs <- list(VAS = spec_garch11, VGS = spec_garch11, GOLD = spec_garch11, VAF = spec_gjr)
multi_spec <- multispec(univariate_specs)

# Fit the four univariate models and check convergence
univariate_fit <- multifit(multispec = multi_spec, data = as.matrix(returns), solver = "hybrid")
univariate_fits <- univariate_fit@fit
names(univariate_fits) <- tickers
convergence <- data.frame(ETF = tickers, Code = vapply(univariate_fits,
  function(fit) as.integer(fit@fit$convergence), integer(1)))
if (any(convergence$Code != 0)) stop("A GARCH fit did not converge.")
garch_parameters <- do.call(rbind, lapply(tickers, function(tk) {
  estimates <- coef(univariate_fits[[tk]])
  data.frame(ETF = tk, Parameter = names(estimates), Estimate = as.numeric(estimates))
}))

# Standardised residuals form the input to the EVT and copula models
Z <- as.data.frame(sapply(univariate_fits, function(fit) as.numeric(residuals(fit, standardize = TRUE))))
names(Z) <- tickers
stopifnot(nrow(Z) == nrow(returns), all(is.finite(as.matrix(Z))))

# One-step-ahead mean and volatility forecasts
forecasts <- lapply(univariate_fits, function(fit) ugarchforecast(fit, n.ahead = 1))
mu <- vapply(forecasts, function(fit) as.numeric(fitted(fit))[1], numeric(1))
sigma_next <- vapply(forecasts, function(fit) as.numeric(sigma(fit))[1], numeric(1))
if (any(!is.finite(c(mu, sigma_next))) || any(sigma_next <= 0)) stop("Invalid marginal forecasts.")
forecast_check <- data.frame(ETF = tickers, Forecast_mean = as.numeric(mu),
                              Forecast_volatility = as.numeric(sigma_next))

# Ljung-Box checks on residuals and squared residuals
residual_check <- do.call(rbind, lapply(tickers, function(tk) {
  do.call(rbind, lapply(c(10, 20), function(lag) {
    data.frame(ETF = tk, Lag = lag,
      Residual_LB_p = Box.test(Z[[tk]], lag = lag, type = "Ljung-Box")$p.value,
      Squared_LB_p = Box.test(Z[[tk]]^2, lag = lag, type = "Ljung-Box")$p.value)
  }))
}))
cat("Data and GARCH fits complete:", nrow(returns), "return observations.\n")

# 4. EVT MARGINS AND STATIC COPULAS

# Fit and check the two tails of each standardised residual series
margins <- lapply(tickers, function(tk) fit_margin(Z[[tk]], tail_p))
names(margins) <- tickers
gpd_table <- margin_table(margins)
check_probs <- sort(unique(c(seq(0.001, 0.999, length.out = 2000), tail_p, 1 - tail_p, 0.01, 0.99)))
inverse_check <- check_margins(margins, check_probs)

# Static copulas are fitted to empirical ranks, not to the EVT CDFs.
U_raw <- sapply(Z, function(z) ecdf(z)(z))
colnames(U_raw) <- tickers
U <- pmin(pmax(U_raw, .Machine$double.eps), 0.99999)
stopifnot(nrow(U) == nrow(Z), ncol(U) == n_assets,
          all(is.finite(U)), all(U > 0 & U < 1))
uniform_check <- data.frame(ETF = tickers, Minimum = apply(U, 2, min),
  Maximum = apply(U, 2, max), Mean = colMeans(U),
  Repeated_residual_values = vapply(Z, function(z) length(z) - length(unique(z)), integer(1)),
  Upper_values_clipped = colSums(U_raw > 0.99999))

# Starting values and fits for Gaussian, Student-t and Clayton copulas
R_start <- cor(qnorm(U))
invisible(chol(R_start))
start_rho <- copula::P2p(R_start)
fit_gaussian <- fitCopula(
  normalCopula(dim = n_assets, dispstr = "un"), data = U, method = "mpl", start = start_rho,
  optim.method = "Nelder-Mead", optim.control = list(maxit = 5000, reltol = 1e-8),
  estimate.variance = FALSE)
fit_student <- fitCopula(
  tCopula(dim = n_assets, dispstr = "un", df = 10, df.fixed = FALSE), data = U, method = "mpl",
  start = c(coef(fit_gaussian), 10), optim.method = "Nelder-Mead",
  optim.control = list(maxit = 5000, reltol = 1e-8,
                       parscale = c(rep(1, length(coef(fit_gaussian))), 10)),
  estimate.variance = FALSE)
fit_clayton <- fitCopula(
  claytonCopula(dim = n_assets), data = U, method = "mpl", start = 0.2,
  optim.method = "Brent", lower = 1e-6, upper = 20, estimate.variance = FALSE)
static_fits <- list(Gaussian = fit_gaussian, Student_t = fit_student, Clayton = fit_clayton)

# Check the copula fits before comparing their pseudo-log-likelihoods
static_fit_check <- data.frame(Model = names(static_fits),
  Convergence = vapply(static_fits, function(fit) as.integer(summary(fit)$convergence), integer(1)),
  Pseudo_loglik = vapply(static_fits, function(fit) as.numeric(logLik(fit)), numeric(1)))
if (any(static_fit_check$Convergence != 0) || any(!is.finite(static_fit_check$Pseudo_loglik))) {
  stop("A static copula fit failed.")
}
R_gauss <- copula::getSigma(fit_gaussian@copula)
R_student <- copula::getSigma(fit_student@copula)
dimnames(R_gauss) <- dimnames(R_student) <- list(tickers, tickers)
correlation_checks <- data.frame(Model = c("Gaussian", "Student_t"), Minimum_eigenvalue = c(
  min(eigen(R_gauss, symmetric = TRUE, only.values = TRUE)$values),
  min(eigen(R_student, symmetric = TRUE, only.values = TRUE)$values)))
if (any(correlation_checks$Minimum_eigenvalue <= 0)) stop("Invalid static correlation matrix.")
student_df <- unname(tail(coef(fit_student), 1))
clayton_theta <- unname(coef(fit_clayton)[1])
if (clayton_theta < 1e-5) warning("Clayton is near its independence boundary.")
if (clayton_theta > 19.99) stop("Clayton reached its upper search bound.")

# Information criteria for the static models (copula likelihood only)
copula_comparison <- do.call(rbind, lapply(names(static_fits), function(model) {
  fit <- static_fits[[model]]
  k <- length(coef(fit))
  ll <- as.numeric(logLik(fit))
  data.frame(Model = model, Parameters = k, Pseudo_loglik = ll,
             AIC = 2 * k - 2 * ll, BIC = log(nrow(U)) * k - 2 * ll)
}))
static_parameters <- do.call(rbind, lapply(names(static_fits), function(model) {
  estimates <- coef(static_fits[[model]])
  data.frame(Model = model, Parameter = names(estimates), Estimate = as.numeric(estimates))
}))

set.seed(seed)

# The CCC test uses its own first-stage filtering; it is not an EVT fit test.
dcc_test <- DCCtest(Data = as.matrix(returns), garchOrder = c(1, 1), n.lags = 1, solver = "solnp")
ccc_table <- data.frame(Statistic = as.numeric(dcc_test$statistic),
                        P_value = format.pval(dcc_test$p.value, digits = 3, eps = 1e-6))
cat("EVT margins and static copulas complete. Student-t df:", round(student_df, 4), "\n")

# 5. DCC GAUSSIAN COPULA

# Use the fitted univariate filters and empirical probability transformation
dcc_spec <- cgarchspec(
  uspec = multi_spec, VAR = FALSE, dccOrder = c(1, 1), asymmetric = FALSE,
  distribution.model = list(copula = "mvnorm", method = "ML", time.varying = TRUE,
                             transformation = "empirical"))
returns_xts <- xts::xts(as.matrix(returns), order.by = return_dates)
set.seed(seed)
dcc_fit <- cgarchfit(
  spec = dcc_spec, data = returns_xts, fit = univariate_fit, solver = "solnp",
  fit.control = list(eval.se = FALSE, stationarity = TRUE, scale = FALSE))
if (!methods::is(dcc_fit, "cGARCHfit")) stop("Unexpected dynamic-copula fit object.")
dcc_convergence <- dcc_fit@mfit$convergence
if (length(dcc_convergence) != 1 || !is.finite(dcc_convergence) || dcc_convergence != 0) {
  stop("The DCC optimizer did not converge.")
}

# The DCC and static models must use the same standardised residuals
Z_dcc <- as.matrix(residuals(dcc_fit)) / as.matrix(sigma(dcc_fit))
if (!identical(dim(Z_dcc), dim(as.matrix(Z)))) stop("Residual dimensions differ.")
colnames(Z_dcc) <- tickers
U_dcc <- apply(Z_dcc, 2, function(z) ecdf(z)(z))
U_dcc <- pmin(pmax(U_dcc, .Machine$double.eps), 0.99999)
input_check <- data.frame(Residual_rows = nrow(Z_dcc),
  Maximum_residual_difference = max(abs(Z_dcc - as.matrix(Z))),
  Maximum_probability_difference = max(abs(U_dcc - U)))
if (any(!is.finite(as.matrix(input_check))) ||
    input_check$Maximum_residual_difference > 1e-8 ||
    input_check$Maximum_probability_difference > 1e-8) stop("Static and DCC inputs differ.")

# DCC adjustment, persistence and fitted correlation path
dcc_coef <- coef(dcc_fit, type = "dcc")
alpha_index <- grep("dcca", names(dcc_coef))
beta_index <- grep("dccb", names(dcc_coef))
if (length(alpha_index) != 1 || length(beta_index) != 1) stop("Unexpected DCC parameters.")
dcc_alpha <- unname(dcc_coef[alpha_index])
dcc_beta <- unname(dcc_coef[beta_index])
dcc_persistence <- dcc_alpha + dcc_beta
if (any(!is.finite(c(dcc_alpha, dcc_beta))) || dcc_alpha < 0 || dcc_beta < 0 || dcc_persistence >= 1) {
  stop("Invalid DCC parameter constraints.")
}
dcc_table <- data.frame(Parameter = c("Alpha", "Beta", "Alpha + Beta"),
                        Estimate = c(dcc_alpha, dcc_beta, dcc_persistence))
R_dcc <- rcor(dcc_fit)
if (length(dim(R_dcc)) != 3 || dim(R_dcc)[1] != n_assets || dim(R_dcc)[2] != n_assets ||
    dim(R_dcc)[3] != nrow(returns) || any(!is.finite(R_dcc))) stop("Invalid DCC correlation path.")
minimum_path_eigenvalue <- min(apply(R_dcc, 3, function(R) {
  min(eigen(R, symmetric = TRUE, only.values = TRUE)$values)
}))
if (minimum_path_eigenvalue <= 0) stop("A historical DCC matrix is not positive definite.")

# Get tomorrow's correlation forecast, rather than using the final in-sample value.
# Check it is independent of the two simulation paths.
dcc_probe <- cgarchsim(dcc_fit, n.sim = 1, n.start = 0, m.sim = 2,
                        startMethod = "sample", rseed = c(seed, seed + 1L), only.density = FALSE)
R_probe_1 <- rcor(dcc_probe, sim = 1)
R_probe_2 <- rcor(dcc_probe, sim = 2)
expected_dimensions <- c(n_assets, n_assets, 1L)
if (!identical(as.integer(dim(R_probe_1)), expected_dimensions) ||
    !identical(as.integer(dim(R_probe_2)), expected_dimensions)) stop("Unexpected forecast dimensions.")
R_next <- R_probe_1[, , 1]
dimnames(R_next) <- list(tickers, tickers)
if (any(!is.finite(R_next))) stop("Non-finite forecast correlations.")
forecast_correlation_check <- data.frame(
  Difference_between_paths = max(abs(R_next - R_probe_2[, , 1])),
  Symmetry_error = max(abs(R_next - t(R_next))), Diagonal_error = max(abs(diag(R_next) - 1)),
  Minimum_eigenvalue = min(eigen(R_next, symmetric = TRUE, only.values = TRUE)$values),
  Minimum_historical_eigenvalue = minimum_path_eigenvalue)
if (forecast_correlation_check$Difference_between_paths > 1e-8 ||
    forecast_correlation_check$Symmetry_error > 1e-8 ||
    forecast_correlation_check$Diagonal_error > 1e-8 ||
    forecast_correlation_check$Minimum_eigenvalue <= 0) stop("DCC forecast verification failed.")
invisible(chol(R_next))

# Summarise fitted correlations for all six ETF pairs
pairs <- combn(seq_along(tickers), 2)
correlation_summary <- do.call(rbind, lapply(seq_len(ncol(pairs)), function(k) {
  i <- pairs[1, k]
  j <- pairs[2, k]
  series <- R_dcc[i, j, ]
  data.frame(Pair = paste(tickers[c(i, j)], collapse = "-"), Static_Gaussian = R_gauss[i, j],
             DCC_mean = mean(series), DCC_minimum = min(series), DCC_maximum = max(series),
             DCC_next = R_next[i, j])
}))
cat("DCC fit and forecast checks complete.\n")

# 6. SIMULATION, TAIL COMPARISONS AND PORTFOLIO RISK

# The same EVT margins and one-day forecasts are used across copula models
U_sim <- simulate_uniforms(static_fits, R_next, M, seed)
shock_sim <- lapply(U_sim, uniforms_to_shocks, margins = margins)
all_sims <- lapply(shock_sim, shocks_to_returns, mu = mu, sigma_next = sigma_next)

# Check that simulated margins and inverse transformations behave as expected
simulation_check <- do.call(rbind, lapply(names(U_sim), function(model) {
  u <- U_sim[[model]]
  data.frame(Model = model, ETF = colnames(u), Uniform_mean = colMeans(u),
             Uniform_SD = apply(u, 2, sd), Lower_1pct_frequency = colMeans(u < 0.01),
             Upper_1pct_frequency = colMeans(u > 0.99))
}))
simulation_inverse_check <- do.call(rbind, lapply(names(U_sim), function(model) {
  errors <- vapply(tickers, function(tk) {
    max(abs(F_cdf(shock_sim[[model]][, tk], margins[[tk]]) - U_sim[[model]][, tk]))
  }, numeric(1))
  if (any(!is.finite(errors)) || max(errors) > 1e-7) stop(model, ": simulated inverse check failed.")
  data.frame(Model = model, Maximum_probability_error = max(errors))
}))
gaussian_targets <- list(Gaussian = R_gauss, DCC_Gaussian = R_next)
simulation_correlation_check <- do.call(rbind, lapply(names(gaussian_targets), function(model) {
  data.frame(Model = model,
    Maximum_correlation_difference = max(abs(cor(qnorm(U_sim[[model]])) - gaussian_targets[[model]])))
}))

# Compare observed co-exceedances against the three static copulas.
# The one-day DCC forecast is not a fitted full-sample benchmark.
observed_exceedance <- exceedance_summary(Z, U, exceedance_probs, min_joint)
model_exceedance <- do.call(rbind, lapply(names(static_fits), function(model) {
  data.frame(Model = model, exceedance_summary(shock_sim[[model]], U_sim[[model]], exceedance_probs, min_joint))
}))

# Marginal (one-asset-conditioned) exceedance correlations
observed_ls <- ls_exceedance_correlation(
  values = Z,
  uniforms = U,
  q = primary_q,
  min_obs = min_joint
)

model_ls <- do.call(rbind, lapply(names(static_fits), function(model) {
  out <- ls_exceedance_correlation(
    values = shock_sim[[model]],
    uniforms = U_sim[[model]],
    q = primary_q,
    min_obs = min_joint
  )
  out$Model <- model
  out
}))

# Lower- and upper-tail co-exceedance rates
observed_tail_dependence <- empirical_tail_dependence(
  uniforms = U,
  u = c(0.05, 0.10)
)

model_tail_dependence <- do.call(rbind, lapply(names(static_fits), function(model) {
  out <- empirical_tail_dependence(
    uniforms = U_sim[[model]],
    u = c(0.05, 0.10)
  )
  out$Model <- model
  out
}))

# Date-block bootstrap intervals at both requested block lengths
bootstrap_results <- do.call(rbind, lapply(block_lengths, function(block_length) {
  cat("Exceedance bootstrap, block length", block_length, "\n")
  bootstrap_exceedance(Z, U, exceedance_probs, min_joint, bootstrap_reps, block_length, seed + block_length)
}))

# Collect the 10% tail comparisons into tables used by the report
primary_observed <- observed_exceedance[observed_exceedance$q == primary_q, ]
primary_comparison <- data.frame(Pair = primary_observed$Pair, Tail = primary_observed$Tail,
  Joint_observations = primary_observed$N_joint, Observed = primary_observed$Correlation)
joint_comparison <- data.frame(Pair = primary_observed$Pair, Tail = primary_observed$Tail,
  Joint_observations = primary_observed$N_joint, Observed = primary_observed$Joint_frequency)
observed_key <- paste(primary_observed$Pair, primary_observed$Tail)
for (model in names(static_fits)) {
  selected <- model_exceedance[model_exceedance$Model == model & model_exceedance$q == primary_q, ]
  index <- match(observed_key, paste(selected$Pair, selected$Tail))
  if (anyNA(index)) stop("Observed and model exceedance rows do not match.")
  primary_comparison[[model]] <- selected$Correlation[index]
  joint_comparison[[model]] <- selected$Joint_frequency[index]
}
sparse_exceedances <- observed_exceedance[observed_exceedance$N_joint < min_joint,
                                           c("Pair", "Tail", "q", "N_joint")]
plot_intervals <- bootstrap_results[bootstrap_results$Block_length == block_lengths[1], ]
primary_intervals <- plot_intervals[plot_intervals$q == primary_q,
  c("Pair", "Tail", "N_joint", "Correlation", "Correlation_lower", "Correlation_upper", "Valid_correlation_bootstraps")]

# Equal-weight VaR/CVaR followed by the long-only 5% allocation grid
w_equal <- setNames(rep(1 / n_assets, n_assets), tickers)
stopifnot(isTRUE(all.equal(unname(var_cvar(-(1:100), 0.95)), c(95, 98), tolerance = 1e-10)))
equal_weight_results <- summarise_risk(all_sims, confidence_levels)
if (any(equal_weight_results$CVaR < equal_weight_results$VaR - 1e-10)) stop("CVaR is smaller than VaR.")
units <- as.integer(round(1 / weight_step))
if (n_assets != 4 || abs(units * weight_step - 1) > 1e-10) stop("Invalid allocation grid settings.")
grid <- expand.grid(w1 = 0:units, w2 = 0:units, w3 = 0:units)
grid <- grid[rowSums(grid) <= units, ]
W <- cbind(as.matrix(grid), units - rowSums(grid)) / units
colnames(W) <- tickers
stopifnot(all(W >= 0), all(W <= 1), all(abs(rowSums(W) - 1) < 1e-10))

# Find the minimum-CVaR weights separately under each dependence model
allocation_fits <- lapply(names(all_sims), function(model) {
  cat("Optimizing", model, "over", nrow(W), "portfolios.\n")
  minimum_cvar(all_sims[[model]], W, allocation_confidence)
})
names(allocation_fits) <- names(all_sims)
allocation_results <- do.call(rbind, lapply(names(allocation_fits), function(model) {
  fit <- allocation_fits[[model]]
  data.frame(Model = model, Confidence = allocation_confidence,
             as.list(fit$weights), VaR = fit$VaR, CVaR = fit$CVaR)
}))
rownames(allocation_results) <- NULL

# Check that each grid optimum is no worse than equal or single-asset weights
allocation_checks <- do.call(rbind, lapply(names(allocation_fits), function(model) {
  fit <- allocation_fits[[model]]
  asset_returns <- all_sims[[model]][, tickers, drop = FALSE]
  equal_risk <- var_cvar(asset_returns %*% w_equal, allocation_confidence)
  single_asset_cvar <- vapply(tickers, function(tk) {
    unname(var_cvar(asset_returns[, tk], allocation_confidence)["CVaR"])
  }, numeric(1))
  if (abs(sum(fit$weights) - 1) > 1e-10 || min(fit$weights) < -1e-10 ||
      fit$CVaR > equal_risk["CVaR"] + 1e-8 || fit$CVaR > min(single_asset_cvar) + 1e-8 ||
      fit$CVaR < fit$VaR - 1e-10) stop(model, ": allocation verification failed.")
  data.frame(Model = model, Weight_sum = sum(fit$weights), Minimum_weight = min(fit$weights),
             Equal_weight_CVaR = unname(equal_risk["CVaR"]), Minimum_CVaR = fit$CVaR,
             Best_single_asset_CVaR = min(single_asset_cvar),
             CVaR_reduction = unname(equal_risk["CVaR"]) - fit$CVaR)
}))

# 7. SENSITIVITY CHECKS

# New random seeds: keep all fitted parameters and baseline weights fixed
seed_risk_list <- allocation_validation_list <- vector("list", length(seed_set))
for (i in seq_along(seed_set)) {
  current_seed <- seed_set[i]
  cat("Simulation seed", current_seed, "\n")
  new_uniforms <- simulate_uniforms(static_fits, R_next, M, current_seed)
  new_shocks <- lapply(new_uniforms, uniforms_to_shocks, margins = margins)
  new_returns <- lapply(new_shocks, shocks_to_returns, mu = mu, sigma_next = sigma_next)
  seed_risk_list[[i]] <- data.frame(Seed = current_seed, summarise_risk(new_returns, confidence_levels))
  allocation_validation_list[[i]] <- do.call(rbind, lapply(names(allocation_fits), function(model) {
    selected_weights <- allocation_fits[[model]]$weights[tickers]
    risk <- var_cvar(new_returns[[model]][, tickers, drop = FALSE] %*% selected_weights, allocation_confidence)
    data.frame(Seed = current_seed, Model = model, VaR = unname(risk["VaR"]), CVaR = unname(risk["CVaR"]))
  }))
}
seed_results <- do.call(rbind, seed_risk_list)
allocation_validation <- do.call(rbind, allocation_validation_list)
seed_mean <- aggregate(cbind(VaR, CVaR) ~ Model + Confidence, seed_results, mean)
seed_sd <- aggregate(cbind(VaR, CVaR) ~ Model + Confidence, seed_results, sd)
names(seed_mean)[3:4] <- c("VaR_mean", "CVaR_mean")
names(seed_sd)[3:4] <- c("VaR_SD", "CVaR_SD")
seed_summary <- merge(seed_mean, seed_sd, by = c("Model", "Confidence"))
seed_summary_99 <- seed_summary[seed_summary$Confidence == 0.99, ]
allocation_validation_summary <- do.call(rbind, lapply(names(allocation_fits), function(model) {
  selected <- allocation_validation[allocation_validation$Model == model, ]
  data.frame(Model = model, Baseline_CVaR = allocation_fits[[model]]$CVaR,
             New_draw_mean_CVaR = mean(selected$CVaR), New_draw_SD_CVaR = sd(selected$CVaR),
             New_draw_min_CVaR = min(selected$CVaR), New_draw_max_CVaR = max(selected$CVaR))
}))

# Refit the EVT tails at different cut-offs, keeping the copula draws fixed.
# This isolates the marginal-threshold choice from dependence estimation.
threshold_risk_list <- threshold_parameter_list <- threshold_check_list <- vector("list", length(tail_fractions))
for (i in seq_along(tail_fractions)) {
  tp <- tail_fractions[i]
  cat("EVT tail fraction", tp, "\n")
  if (abs(tp - tail_p) < 1e-12) {
    margins_tp <- margins
  } else {
    margins_tp <- lapply(tickers, function(tk) fit_margin(Z[[tk]], tp))
    names(margins_tp) <- tickers
  }
  test_probs <- sort(unique(c(seq(0.001, 0.999, length.out = 1000), tp, 1 - tp, 0.01, 0.99)))
  threshold_check_list[[i]] <- data.frame(Tail_fraction = tp, check_margins(margins_tp, test_probs))
  threshold_parameter_list[[i]] <- data.frame(Tail_fraction = tp, margin_table(margins_tp))
  shocks_tp <- lapply(U_sim, uniforms_to_shocks, margins = margins_tp)
  returns_tp <- lapply(shocks_tp, shocks_to_returns, mu = mu, sigma_next = sigma_next)
  threshold_risk_list[[i]] <- data.frame(Tail_fraction = tp, summarise_risk(returns_tp, confidence_levels))
}
threshold_results <- do.call(rbind, threshold_risk_list)
threshold_parameters <- do.call(rbind, threshold_parameter_list)
threshold_checks <- do.call(rbind, threshold_check_list)
threshold_results_99 <- threshold_results[threshold_results$Confidence == 0.99, ]
baseline_threshold <- threshold_results[abs(threshold_results$Tail_fraction - tail_p) < 1e-12,
                                       c("Model", "Confidence", "VaR", "CVaR")]
baseline_comparison <- merge(equal_weight_results, baseline_threshold, by = c("Model", "Confidence"),
                             suffixes = c("_original", "_threshold_check"))
if (nrow(baseline_comparison) != nrow(equal_weight_results)) stop("Missing baseline comparison rows.")
baseline_difference <- max(abs(c(
  baseline_comparison$VaR_original - baseline_comparison$VaR_threshold_check,
  baseline_comparison$CVaR_original - baseline_comparison$CVaR_threshold_check)))
if (!is.finite(baseline_difference) || baseline_difference > 1e-10) stop("Baseline reproduction failed.")

# Compare uncertainty intervals for 10-day and 20-day blocks
intervals_10 <- bootstrap_results[bootstrap_results$Block_length == 10 & bootstrap_results$q == primary_q,
  c("Pair", "Tail", "Correlation", "Correlation_lower", "Correlation_upper")]
intervals_20 <- bootstrap_results[bootstrap_results$Block_length == 20 & bootstrap_results$q == primary_q,
  c("Pair", "Tail", "Correlation_lower", "Correlation_upper")]
interval_comparison <- merge(intervals_10, intervals_20, by = c("Pair", "Tail"), suffixes = c("_10", "_20"))

# If an earlier analysis was saved, compare its main numerical results.
# This uses the saved object and does not rerun those earlier fits.
reference_file <- file.path(folder, "final_model_results", "final_analysis.rds")
cleanup_check <- NULL
if (file.exists(reference_file)) {
  reference <- readRDS(reference_file)
  same_result <- function(x, y) {
    isTRUE(all.equal(x, y, tolerance = 1e-6, check.attributes = FALSE))
  }
  cleanup_check <- data.frame(
    Check = c("Equal-weight risk", "Allocations", "DCC forecast", "Static coefficients"),
    Matches = c(
      same_result(equal_weight_results, reference$equal_weight_results),
      same_result(allocation_results, reference$allocation_results),
      same_result(R_next, reference$R_next),
      same_result(lapply(static_fits, coef), lapply(reference$static_fits, coef))
    )
  )
  print(cleanup_check)
  if (!all(cleanup_check$Matches)) {
    stop("The cleaned run differs from the saved working analysis. Compare the results before using it.")
  }
} else {
  message("No previous final checkpoint found; result equivalence was not checked.")
}

# 8. PLOTS, TABLES AND SAVED RESULTS

# GPD Q-Q plots and mean-excess plots for each ETF and tail
png(file.path(output_folder, "gpd_qq_plots..png"), width = 6, height = 4, units = "in", res = 300)
par(mfrow = c(2, 4), mar = c(4, 4, 3, 1))
for (side in c("Lower", "Upper")) {
  for (tk in tickers) {
    z <- Z[[tk]]
    m <- margins[[tk]]
    y <- if (side == "Lower") m$uL - z[z < m$uL] else z[z > m$uR] - m$uR
    g <- if (side == "Lower") m$gL else m$gR
    plot(gpd_inverse(1 - ppoints(length(y)), g), sort(y), pch = 19, cex = 0.5,
         main = paste(tk, side), xlab = "Fitted GPD quantile", ylab = "Observed excess")
    abline(0, 1, col = "firebrick", lwd = 2)
  }
}
dev.off()
png(file.path(output_folder, "mean_excess_plots.png"), width = 6, height = 4, units = "in", res = 300)
par(mfrow = c(2, 4), mar = c(4, 4, 3, 1))
for (side in c("Lower", "Upper")) {
  for (tk in tickers) {
    x <- if (side == "Lower") -Z[[tk]] else Z[[tk]]
    thresholds <- quantile(x, seq(0.80, 0.98, by = 0.01), names = FALSE)
    me <- sapply(thresholds, function(u) mean(x[x > u] - u))
    plot(thresholds, me, type = "b", pch = 19, cex = 0.6, main = paste(tk, side),
         xlab = "Threshold", ylab = "Mean excess")
    chosen <- if (side == "Lower") -margins[[tk]]$uL else margins[[tk]]$uR
    abline(v = chosen, col = "firebrick", lty = 2)
  }
}
dev.off()

# Historical DCC correlations, with the static Gaussian fit as a reference
png(file.path(output_folder, "dcc_correlations.png"), width = 6, height = 4, units = "in", res = 300)
par(mfrow = c(2, 3), mar = c(4, 4, 3, 1))
for (k in seq_len(ncol(pairs))) {
  i <- pairs[1, k]
  j <- pairs[2, k]
  plot(return_dates, R_dcc[i, j, ], type = "l", col = "#3572A5", ylim = c(-1, 1),
       main = paste(tickers[c(i, j)], collapse = "-"), xlab = "Date", ylab = "Latent Gaussian correlation")
  abline(h = R_gauss[i, j], col = "firebrick", lty = 2)
  abline(h = 0, col = "grey75", lty = 3)
  if (k == 1) legend("bottomleft", c("DCC", "Static Gaussian"),
                    col = c("#3572A5", "firebrick"), lty = c(1, 2), bty = "n", cex = 0.75)
}
dev.off()

# Tail-exceedance correlations and the bootstrap intervals
colours <- c(Gaussian = "#3572A5", Student_t = "#B45F06", Clayton = "#6A4C93")
for (side in c("Lower", "Upper")) {
  png(file.path(output_folder, paste0(tolower(side), "_exceedance_correlations.png")), width = 6, height = 4, units = "in", res = 300)
  par(mfrow = c(2, 3), mar = c(4, 4, 3, 1))
  for (pair in unique(observed_exceedance$Pair)) {
    observed <- plot_intervals[plot_intervals$Pair == pair & plot_intervals$Tail == side, ]
    observed <- observed[order(observed$q), ]
    plot(observed$q, observed$Correlation, type = "n", ylim = c(-1, 1), main = pair,
         xlab = "Marginal tail fraction q", ylab = "Residual exceedance correlation")
    valid <- is.finite(observed$Correlation_lower) & is.finite(observed$Correlation_upper)
    if (any(valid)) arrows(observed$q[valid], observed$Correlation_lower[valid],
                           observed$q[valid], observed$Correlation_upper[valid],
                           angle = 90, code = 3, length = 0.03, col = "grey55")
    for (model in names(static_fits)) {
      selected <- model_exceedance[model_exceedance$Model == model &
        model_exceedance$Pair == pair & model_exceedance$Tail == side, ]
      selected <- selected[order(selected$q), ]
      lines(selected$q, selected$Correlation, col = colours[model], lwd = 2)
    }
    lines(observed$q, observed$Correlation, type = "b", pch = 19)
    abline(h = 0, col = "grey80", lty = 3)
    if (pair == unique(observed_exceedance$Pair)[1]) {
      legend("bottomleft", c("Observed", names(colours)), col = c("black", colours),
             lty = c(1, 1, 1, 1), pch = c(19, NA, NA, NA), bty = "n", cex = 0.65)
    }
  }
  dev.off()
}

# Format tables for the LaTeX report. Captions and filenames stay as they are.
sample_table <- sample_info
sample_table$Start <- format(sample_table$Start, "%d %b %Y")
sample_table$End <- format(sample_table$End, "%d %b %Y")
descriptive_table <- data.frame(ETF = rownames(table1), table1, row.names = NULL)
residual_table <- residual_check
residual_table$Residual_LB_p <- format.pval(residual_check$Residual_LB_p, digits = 3, eps = 0.001)
residual_table$Squared_LB_p <- format.pval(residual_check$Squared_LB_p, digits = 3, eps = 0.001)
names(residual_table) <- c("ETF", "Lag", "Residual p-value", "Squared-residual p-value")
inverse_table <- inverse_check
inverse_table$Maximum_inverse_error <- formatC(inverse_check$Maximum_inverse_error, format = "e", digits = 2)
simulation_inverse_table <- simulation_inverse_check
simulation_inverse_table$Maximum_probability_error <- formatC(
  simulation_inverse_check$Maximum_probability_error, format = "e", digits = 2)
allocation_table <- allocation_results[, c("Model", tickers, "VaR", "CVaR")]
allocation_table[, tickers] <- 100 * allocation_table[, tickers]

# Write every report table to the output folder
save_latex(sample_table, "sample_info.tex", "Common ETF return sample.", "tab:sample", 0)
save_latex(data_audit, "data_audit.tex", "Price-data availability and sample alignment.", "tab:data-audit", 0)
save_latex(descriptive_table, "descriptive_statistics.tex",
           "Descriptive statistics of daily ETF log returns, in percentage points.", "tab:descriptive", 4)
save_latex(garch_parameters, "garch_parameters.tex", "Estimated univariate volatility-model parameters.", "tab:garch", 6)
save_latex(forecast_check, "marginal_forecasts.tex",
           "One-step-ahead marginal mean and volatility forecasts, in percentage points.", "tab:marginal-forecasts", 4)
save_latex(residual_table, "residual_checks.tex",
           "Ljung--Box diagnostic p-values for standardized residuals and their squares.", "tab:residual-checks", 0)
save_latex(gpd_table, "gpd_parameters.tex",
           "GPD estimates for standardized residual tails. The nominal tail fraction is 0.10.",
           "tab:gpd", c(0, 0, 0, 4, 0, 4, 4))
save_latex(inverse_table, "marginal_inverse_checks.tex",
           "Numerical consistency of marginal CDFs and inverses.", "tab:inverse-checks", 0)
save_latex(uniform_check, "empirical_probability_checks.tex",
           "Checks on empirical probabilities used for copula estimation.", "tab:empirical-probabilities", 4)
save_latex(copula_comparison, "static_copula_comparison.tex",
           "Static copula comparison based on a common empirical transformation and copula pseudo-log-likelihood.",
           "tab:static-copulas", c(0, 0, 0, 3, 3, 3))
save_latex(static_parameters, "static_copula_parameters.tex", "Estimated static copula parameters.", "tab:static-parameters", 4)
save_latex(ccc_table, "constant_correlation_test.tex",
           "Engle--Sheppard constant-correlation test using separate package first-stage filtering.", "tab:constant-correlation", 4)
save_latex(dcc_table, "dcc_parameters.tex", "Estimated DCC Gaussian-copula parameters.", "tab:dcc-parameters", 4)
save_latex(correlation_summary, "correlation_summary.tex",
           "Static and dynamic latent Gaussian correlations; the last column is the next-period forecast.", "tab:correlation-summary", 3)
save_latex(simulation_check, "simulation_marginal_checks.tex",
           "Simulated uniform checks. References are mean 0.5, SD 0.2887 and each tail frequency 0.01.", "tab:simulation-margins", 4)
save_latex(simulation_inverse_table, "simulation_inverse_checks.tex",
           "Numerical consistency of simulated EVT marginal transformations.", "tab:simulation-inverses", 0)
save_latex(simulation_correlation_check, "simulation_correlation_checks.tex",
           "Maximum differences between target and simulated latent Gaussian correlations.", "tab:simulation-correlations", 4)
save_latex(primary_comparison, "exceedance_correlation_comparison.tex",
           "Residual exceedance correlations at the 10 percent marginal probability threshold; withheld below 20 joint observations.",
           "tab:exceedance-correlations", c(0, 0, 0, 0, 3, 3, 3, 3))
save_latex(joint_comparison, "joint_tail_frequency_comparison.tex",
           "Joint-event frequencies at the 10 percent marginal probability threshold.",
           "tab:joint-tail-frequencies", c(0, 0, 0, 0, 4, 4, 4, 4))
save_latex(primary_intervals, "exceedance_correlation_intervals.tex",
           "Pointwise 95 percent correlation intervals at the 10 percent threshold, using blocks of 10 dates. Intervals condition on fitted filters and fixed empirical probabilities.",
           "tab:exceedance-intervals", c(0, 0, 0, 0, 3, 3, 3, 0))
save_latex(
  observed_ls,
  "marginal_exceedance_correlations_observed.tex",
  "Marginal exceedance correlations of standardised residuals at the 10 percent tail threshold. Correlations are calculated conditional on one ETF being in the lower or upper tail.",
  "tab:marginal-exceedance-observed",
  c(0, 0, 0, 0, 0, 3, 3, 3, 3)
)

save_latex(
  model_ls,
  "marginal_exceedance_correlations_models.tex",
  "Model-implied marginal exceedance correlations at the 10 percent tail threshold.",
  "tab:marginal-exceedance-models",
  c(0, 0, 0, 0, 0, 0, 3, 3, 3, 3)
)

save_latex(
  observed_tail_dependence,
  "empirical_tail_dependence_observed.tex",
  "Empirical lower- and upper-tail dependence estimates for standardised-residual probabilities.",
  "tab:tail-dependence-observed",
  c(0, 0, 2, 4, 4)
)

save_latex(
  model_tail_dependence,
  "empirical_tail_dependence_models.tex",
  "Model-implied lower- and upper-tail dependence estimates.",
  "tab:tail-dependence-models",
  c(0, 0, 0, 2, 4, 4)
)
save_latex(equal_weight_results, "equal_weight_portfolio_risk.tex",
           "One-day model-implied equal-weight VaR and CVaR, in percentage points. Confidence levels are fractions.",
           "tab:equal-weight-risk", c(0, 0, 2, 4, 4))
save_latex(allocation_table, "minimum_cvar_allocations.tex",
           "Minimum-CVaR allocations at 99 percent confidence on a 5-percentage-point grid. Weights are percentages; risk is daily percentage points. Portfolios are long-only, fully invested and have no return target.",
           "tab:minimum-cvar", c(0, 0, 0, 0, 0, 0, 4, 4))
save_latex(allocation_checks, "allocation_checks.tex",
           "Grid-optimum checks; CVaR reductions are relative to equal weights under the same model.", "tab:allocation-checks", 4)
save_latex(seed_summary_99, "simulation_seed_sensitivity.tex",
           "99 percent equal-weight risk across five new simulation seeds, with fitted parameters fixed.", "tab:seed-sensitivity", 4)
save_latex(allocation_validation_summary, "allocation_simulation_validation.tex",
           "Risk of fixed baseline allocations on new draws. This measures Monte Carlo variation, not out-of-sample investment performance.",
           "tab:allocation-validation", 4)
save_latex(threshold_results_99, "evt_threshold_sensitivity.tex",
           "99 percent equal-weight risk across EVT tail fractions. Dependence and simulated uniforms are fixed; marginal tails are refitted.",
           "tab:threshold-sensitivity", 4)
save_latex(threshold_parameters, "threshold_gpd_parameters.tex", "GPD estimates across EVT tail fractions.",
           "tab:threshold-parameters", c(0, 2, 0, 0, 4, 0, 4, 4))
save_latex(interval_comparison, "bootstrap_block_sensitivity.tex",
           "Pointwise 95 percent exceedance-correlation intervals using blocks of 10 and 20 dates at the 10 percent threshold.",
           "tab:block-sensitivity", 3)

# Keep the fitted objects, simulation draws, checks and tables together.
# A single RDS file makes it easier to revisit the results.
analysis <- list(
  settings = list(
    tickers = tickers,
    sample_dates = range(return_dates),
    observations = nrow(returns),
    baseline_tail_fraction = tail_p,
    simulations = M,
    baseline_seed = seed,
    sensitivity_seeds = seed_set,
    confidence_levels = confidence_levels,
    allocation_confidence = allocation_confidence,
    weight_step = weight_step,
    bootstrap_reps = bootstrap_reps,
    block_lengths = block_lengths,
    exceedance_probs = exceedance_probs,
    primary_q = primary_q,
    min_joint = min_joint,
    tail_fractions = tail_fractions,
    RNG = RNGkind()
  ),
  prices = prices,
  returns = returns,
  return_dates = return_dates,
  Z = Z,
  U = U,
  multi_spec = multi_spec,
  univariate_fit = univariate_fit,
  margins = margins,
  static_fits = static_fits,
  dcc_fit = dcc_fit,
  R_dcc = R_dcc,
  R_next = R_next,
  mu = mu,
  sigma_next = sigma_next,
  simulations = list(
    U_sim = U_sim,
    shock_sim = shock_sim,
    all_sims = all_sims
  ),
  checks = list(
    data_audit = data_audit,
    convergence = convergence,
    residual_check = residual_check,
    inverse_check = inverse_check,
    uniform_check = uniform_check,
    static_fit_check = static_fit_check,
    correlation_checks = correlation_checks,
    input_check = input_check,
    forecast_correlation_check = forecast_correlation_check,
    simulation_check = simulation_check,
    simulation_inverse_check = simulation_inverse_check,
    simulation_correlation_check = simulation_correlation_check,
    allocation_checks = allocation_checks,
    threshold_checks = threshold_checks,
    baseline_difference = baseline_difference,
    cleanup_check = cleanup_check
  ),
  tables = list(
    sample_info = sample_info,
    descriptive = table1,
    garch_parameters = garch_parameters,
    forecast_check = forecast_check,
    gpd_table = gpd_table,
    copula_comparison = copula_comparison,
    static_parameters = static_parameters,
    ccc_table = ccc_table,
    dcc_table = dcc_table,
    correlation_summary = correlation_summary
  ),
  dcc_test = dcc_test,
  observed_exceedance = observed_exceedance,
  model_exceedance = model_exceedance,
  bootstrap_results = bootstrap_results,
  primary_comparison = primary_comparison,
  joint_comparison = joint_comparison,
  sparse_exceedances = sparse_exceedances,
  interval_comparison = interval_comparison,
  equal_weight_results = equal_weight_results,
  W = W,
  allocation_results = allocation_results,
  allocation_fits = allocation_fits,
  seed_results = seed_results,
  seed_summary = seed_summary,
  allocation_validation = allocation_validation,
  allocation_validation_summary = allocation_validation_summary,
  threshold_results = threshold_results,
  threshold_parameters = threshold_parameters
)

# Save the full analysis and the R session information
saveRDS(analysis, file.path(output_folder, "final_analysis.rds"))
capture.output(
  sessionInfo(),
  file = file.path(output_folder, "session_info.txt")
)

# 9. ROBUST STANDARD ERRORS FOR THE GARCH PARAMETERS

# Read the saved fits and export their robust coefficient table
results_folder <- "/Users/manya/Desktop/Financial/Data/clean_final_results"
fit_results <- readRDS(file.path(results_folder, "final_analysis.rds"))
fits <- fit_results$univariate_fit@fit
names(fits) <- fit_results$settings$tickers

robust_garch_table <- do.call(rbind, lapply(names(fits), function(etf) {
  mat <- fits[[etf]]@fit$robust.matcoef
  if (is.null(mat) || !is.matrix(mat) || ncol(mat) < 4) {
    warning("Robust parameter covariance unavailable for ", etf)
    return(NULL)
  }
  data.frame(
    ETF = etf,
    Parameter = rownames(mat),
    Estimate = as.numeric(mat[, 1]),
    Robust_SE = as.numeric(mat[, 2]),
    Robust_p_value = as.numeric(mat[, 4]),
    row.names = NULL
  )
}))

if (is.null(robust_garch_table) || nrow(robust_garch_table) == 0) {
  stop("No GARCH robust standard errors available in the saved fits.")
}

# Omega is implied by variance targeting, so its robust SE can be NA.
write.csv(robust_garch_table,
          file.path(results_folder, "garch_robust_standard_errors.csv"),
          row.names = FALSE)

# Save a LaTeX version of the same robust standard-error table
if (requireNamespace("xtable", quietly = TRUE)) {
  latex_table <- xtable::xtable(robust_garch_table,
                                caption = "Univariate GARCH estimates and robust standard errors (NA where unavailable).",
                                label = "tab:garch-robust-se", digits = 4)
  print(latex_table, type = "latex",
        file = file.path(results_folder, "garch_robust_standard_errors.tex"),
        include.rownames = FALSE, booktabs = TRUE,
        caption.placement = "top", comment = FALSE)
}
print(robust_garch_table)
