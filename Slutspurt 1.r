##Master code
install.packages("sandwich")
library(epo)
library(Matrix)
library(lubridate)
library(dplyr)
library(zoo)
library(timeDate)
library(tidyr)
library(stringr)
library(ggplot2)
library(xtable)
library(readr)
library(sandwich)


##################################################################################
#Henter månedlig data
data_monthly = read.csv("C:/Users/nikol/OneDrive - CBS - Copenhagen Business School/Bachelor/Data/49_Industry_Portfolios_Monthly_Value.csv", header = TRUE, sep=",")

names(data_monthly)[names(data_monthly) == "Year"] <- "Date"

#Laver det om til dato format - Den først representere hele måneden
data_monthly$Date <- as.Date(paste0(data_monthly$Date, "01"), format = "%Y%m%d")

#Erstatter ugyldige værider med NA
for (i in 2:ncol(data_monthly)) {
  data_monthly[[i]][data_monthly[[i]] == -99.99 | data_monthly[[i]] == -999] <- NA
}

#Antal NA værdier i datasættet
colSums(is.na(data_monthly))

#Henter renterne igen 
## Kenneth French: 1 month T-Bill (risk free rate)
rf_månedlig = read.csv("C:/Users/nikol/OneDrive - CBS - Copenhagen Business School/Bachelor/Data/3_Industry_Portfolios_RF.csv", header = TRUE, sep=",")
rf_månedlig <- rf_månedlig %>% select(c(Year,RF))
#View(rf)
#Omformatere RF
names(rf_månedlig)[names(rf_månedlig) == "Year"] <- "Date"
rf_månedlig$Date <- ymd(paste0(rf_månedlig$Date, "01"))

#Sætter RF_monthly sammen med data monthly
data_monthly <- left_join(data_monthly, rf_månedlig, by = "Date")

Unfiltered_data_monthly <- data_monthly

#Skal der bruges excess return
data_monthly_log <- Unfiltered_data_monthly %>% mutate(across(-c(Date,RF),~( . -RF)))
data_monthly_log<-data_monthly_log %>% mutate(across(-c(Date), ~(log (1+ . / 100))))

SR_test_data <- Unfiltered_data_monthly %>% mutate(across(-(Date), ~(log(1+./100))))

data_procent_monthly <- data_monthly %>% mutate(across(-c(Date), ~ (1+ . / 100)))
data_monthly<-data_monthly %>% mutate(across(-c(Date, RF), ~(log (1+ . / 100))))



#Usikker på dette, om RF skal laves om til decimal afkast??????????
#data_monthly<-data_monthly %>% mutate(across(RF, ~(log(1+ . / 100))))


# Signaler ----------------------------------------------------------------
#Laver funktion til at finde signal

########################################################################
#TSMOM
TSMOM <- function(Current_date, active_assets){
  active_data <- data_monthly_log %>% select(all_of(c("Date", active_assets))) %>%
    filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
    select(-c(Date))

  sd_aktiv <- active_data %>% summarise(across(everything(),sd))

  sign <- sapply(active_data, function(x) {
    if (sum(x, na.rm = TRUE) > 0) 1 else -1
  })

  signal <- 0.1*sd_aktiv*sign
  signal <- as.numeric(signal[1, ])

  return(signal)
}

##########################################################################
## XSMOM
Current_date <- as.Date("1942-01-30")

XSMOM <- function(Current_date, active_assets) {  
  #Transformer data - kun ikke NA aktiver og et år tilbage
  past_data <- data_monthly_log %>%
    select(all_of(c("Date", active_assets))) %>%
    filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
    select(-c(Date))
  
  #Finder afkastet for hvert aktiv over den sidste periode
  rtn_i <- apply(past_data, 2, function(x) sum(x))
  
  mu <- mean(as.numeric(rtn_i))
  s_i <- as.numeric(rtn_i) - mu

  #Finder summen til de postive afkast
  pos_sum <- sum(s_i[s_i > 0])

  #Finder C ved begrænsning fra linje 25
  c_t <- 1 / sum((pos_sum))

  #Ganger C på signalet
  signal <- c_t * s_i
  
  #Sætter navne på signalet
  names(signal) <- active_assets
  return(signal)
}

############################################################################
#Risiko model
Risk_model_monthly  <- function(Current_date, window, theta, active_assets){
  active_data <- data_monthly_log %>% select(all_of(c(("Date"),active_assets)))%>%
   filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
   select(-c(Date))
  
  cov_matrix <- cov(active_data, use = "pairwise.complete.obs")
  
  # Compute asset varains
  sigma <- diag(sqrt(diag(cov_matrix)))
  
  # Compute the correlation matrix
  Omega <- solve(sigma) %*% cov_matrix %*% solve(sigma)
  
  # Eigendecompose Omega
  eig <- eigen(Omega)
  P <- eig$vectors
  D <- diag(eig$values)
  dimI <- nrow(D)

  lowD <- min(diag(D))

  highD <- max(diag(D))
  MaxDiffD <- highD/lowD

  # Shrink the eigenvalues
  Dtilde <- (1 - theta) * D + theta * diag(dimI)

  lowDtilde <- min(diag(Dtilde))

  highDtilde <- max(diag(Dtilde))
  MaxDiffDtilde <- highDtilde/lowDtilde
  
  # Reconstruct the shrunk correlation matrix: Omegatilde = P Dtilde Pᵀ
  Omegatilde <- P %*% Dtilde %*% t(P)  
  
  # Reconstruct the adjusted covariance matrix: Sigma_tilde = sigma * Omegatilde * sigma
  Sigmatilde <- sigma %*% Omegatilde %*% sigma

  return(list(Sigmatilde = Sigmatilde,lowD=lowD,lowDtilde=lowDtilde, MaxDiffD = MaxDiffD, MaxDiffDtilde = MaxDiffDtilde))
}
risk_model <- Sigmatilde
# EPO ---------------------------------------------------------------------
##Simpel EPO
simple_EPO <- function(Current_date, signal, risk_model, gamma, w, window, active_assets, months) {
  active_data <- data_monthly_log %>% select(all_of(c(("Date"),active_assets)))%>%
   filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
   select(-c(Date))

  V <- diag(diag(cov(active_data, use = "pairwise.complete.obs")))

  V <- as.matrix(V)
  #V <- diag(diag(risk_model))
  
  risk_model <- as.matrix(risk_model)

  Sigma_w <-(1 - w) * risk_model + w * V

  Sigma_w <- as.matrix(Sigma_w)

  EPO <- ((1/gamma)*solve(Sigma_w)%*%signal)
  weights <- EPO #/ (sum(abs(EPO))) #normalizere vægte
  names(weights) <- names(signal)
  return(weights)
}

##Simpel EPO
anker_EPO <- function(Current_date, signal, risk_model, gamma, w, window, active_assets, months) {
  active_data <- data_monthly_log %>% select(all_of(c(("Date"),active_assets)))%>%
   filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
   select(-c(Date))

  V <- diag(diag(cov(active_data, use = "pairwise.complete.obs")))
  
  V <- as.matrix(V)
  #V <- diag(diag(risk_model))

  a <- rep(1 / ncol(V), ncol(V))

  Sigma_w <-(1 - w) * risk_model + w * V

  Sigma_w <- as.matrix(Sigma_w)
  risk_model <- as.matrix(risk_model)

  EPO <-  as.numeric((1-w) * ((sqrt(t(a) %*% risk_model %*% a)) / sqrt((t(signal) %*% solve(Sigma_w)) %*% risk_model %*% (solve(Sigma_w) %*% signal)))) * solve(Sigma_w) %*% signal +  w * solve(Sigma_w) %*% V %*% a

  weights <- EPO #/ (sum(abs(EPO))) #normalizere vægte
  names(weights) <- names(signal)
  return(weights)
}
############################################################################
#Indsæt værdier til risiko model
window <- 120
theta <- 0.05
gamma <- 3
w <- 0.25

###########################################################################
#Giver inpunts til rebalancerings portefølje
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)


#Danner dataframe til at gemme SR samt den laveste egenværdi til et givet vindue
#SR_daglig <- data.frame(w=numeric(),Sharpe =numeric())
#SR_årlig_ex <- data.frame(w=numeric(),window=numeric(),Sharpe =numeric())
#SR_årlig <- data.frame(w=numeric(),window=numeric(),Sharpe =numeric())
LowD <- data.frame(window=numeric(),DV=numeric())
LowDtilde <- data.frame(window=numeric(),DtildeV=numeric())

#liste over givet vinduer samt w'er der ønskes at teste for
window_list <- c(60,90,120)
w_list <- c(0)
#,0.1,0.25,0.5,0.75,0.9,0.99,1
#Opret kenneth 

#Matrix til SR værdier
sharpe_matrix <- matrix(NA, nrow = length(w_list), ncol = length(window_list),
                        dimnames = list(paste0("w=", w_list), paste0("window=", window_list)))

signal_type <- "TSMOM"

#For loop der tester for alle givet w'er og vinduer
for (i in seq_along(window_list)){
    window <- window_list[i]

  asset_names <- names(data_monthly)[2:50]
  weights <- data.frame(
    Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(BacktestDates), ncol = length(asset_names))),
      asset_names
    )
  )  
  for (j in seq_along(w_list)){
    w <- w_list[j]
      for (k in 1:(nrow(weights))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
        Current_date <- weights$Dates[k]  # ultimo måned t

        # 1. Data til signal og risiko
        #Her gemmes datoerne fra et år siden
        signal_data_monthly <- data_monthly_log %>%
            filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
            select(all_of(asset_names))
        
        risk_data_monthly <- data_monthly_log %>%
            filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
            select(all_of(asset_names))
        
        # 2. Find aktiver uden NA’er i begge vinduer
        valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
        valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
        active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
        
        # 3. Udregn signal, risikomodel og vægte
        if (signal_type=="TSMOM"){
          signal <- TSMOM(Current_date, active_assets)
        } else if (signal_type=="XSMOM"){
          signal <- XSMOM(Current_date, active_assets)
        } else if (signal_type=="Col"){
          signal <- CMean(Current_date, active_assets)
        } else {
          print("Not acceptable signal")
        }
        risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde
        w_t <- simple_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
        
        # 4. Gem vægtene på datoen for næste måned
        weights[k, active_assets] <- w_t

        if(k %% 300 ==0){
            print(k)
            cat("out of: ")
            print(nrow(weights))
        }
      }
      
      #Gemmer det i en ny dataframe, for at opretholde "raw" udregninger
      #weightsmaster <- weights
      ######################################################
      #Laver dato rækken til dato format
      weights <- weights %>%
      mutate(Dates = as.Date(Dates))
      A <- weights
      names(A)[names(A) == "Dates"] <- "Date"
      #Finder mængden investeret i det riskiofrie aktiv
      
      A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
      A <- A %>% mutate(rf_weight = 0)
      #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
      B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
      #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
      AB <- left_join(A,B,by="Date") 
      AB <- AB %>%
          mutate(across(everything(), ~replace_na(., 0)))
      AB <- AB %>% rename(
      rf.x =rf_weight,
      rf.y = RF
      )
      Afkast <- AB %>% select(ends_with(".y"))
      Weights_test <- AB %>% select(ends_with(".x"))
      colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
      colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
      stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
      Results <- Afkast * Weights_test
      AB_final <- bind_cols(AB %>% select(Date), Results)
      AB_final <- AB_final %>%
        mutate(Afkast = rowSums(select(., -Date)))
      Afkast <- AB_final %>% select(Date, Afkast)

      annual_SR <- (mean(Afkast$Afkast)/sd(Afkast$Afkast))*sqrt(12)

      #Laver afkast om til årligt afkast OBS. virker når afkast er i log
    #   Afkast_Årligt <- Afkast %>%
    #       mutate(Year = lubridate::year(Date)) %>%
    #       select(-Date) %>%
    #       group_by(Year) %>%
    #       summarise(across(everything(), ~ exp(sum(., na.rm = TRUE))-1)) %>%
    #       as.data.frame()

      sharpe_matrix[j, i] <- annual_SR
      
      cat("For w = ", w, "\n")
      cat("For windue = ", window, "\n")
    }
}
 
View(sharpe_matrix)
LateX_SR_Table <- xtable(sharpe_matrix, caption = "SR PF1-4", digits = 2)
print(LateX_SR_Table, type="latex", caption.placement = "top", include.rownames = TRUE, digits =2 )

##########################################################################################
#INDMOM
asset_names <- names(data_monthly)[2:50]

INDMOM_wheigts <- data.frame(
    Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(0, nrow = nrow(BacktestDates), ncol = length(asset_names))),
      asset_names
    ))

for(i in 1:nrow(INDMOM_wheigts)){
  Current_date <- INDMOM_wheigts$Dates[i]  # ultimo måned t

  # 1. Data til signal og risiko
  #Her gemmes datoerne fra et år siden
  signal_data_monthly <- data_monthly_log %>%
    filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
    select(all_of(asset_names))

  # 2. Find aktiver uden NA’er i begge vinduer
  valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
  active_assets <- asset_names[valid_signal_assets]

  signal <- XSMOM(Current_date, active_assets)

  ord <- sort(signal,decreasing = FALSE)

  bot5 <- names(ord) [1:5]
  top5 <- names(ord) [(length(ord)-4):length(ord)]

  w <- setNames( rep(0, length(signal)), names(signal) )

  w[top5] <- 1/5
  w[bot5] <- -1/5

  INDMOM_wheigts[i,active_assets] <- w
}

raw_afkast <- data_monthly_log %>% 
    filter(EndBackTest >= Date & Date >= StartBackTest) 

raw_afkast <- raw_afkast %>% mutate(across(everything(), ~replace_na(., 0)))
raw_afkast <- raw_afkast %>% select(-RF)

montly_afkast <- raw_afkast[,-1] * INDMOM_wheigts[,-1]

montly_afkast <- montly_afkast %>% mutate(Afkast = rowSums(.))

montly_afkast_trimmed <- bind_cols(raw_afkast %>% select(Date), montly_afkast %>% select(Afkast))

(mean(montly_afkast_trimmed$Afkast)/sd(montly_afkast_trimmed$Afkast))*sqrt(12)
# Afkast_Årligt <- montly_afkast_trimmed %>%
#     mutate(Year = lubridate::year(Date)) %>%
#     select(-Date) %>%
#     group_by(Year) %>%
#     summarise(across(everything(), ~ exp(sum(., na.rm = TRUE))-1)) %>%
#     as.data.frame()

mean(Afkast_Årligt[,2])/sd(Afkast_Årligt[,2])

afkast_INDMOM <- montly_afkast_trimmed %>% mutate(across(Afkast, ~(exp(.)-1)))

################################################################
#anker
############################################################################
#Indsæt værdier til risiko model
theta <- 0.05
gamma <- 3


###########################################################################
#Giver inpunts til rebalancerings portefølje
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)

#liste over givet vinduer samt w'er der ønskes at teste for
window_list <- c(60)
w_list <- c(0)


#Matrix til SR værdier
sharpe_matrix <- matrix(NA, nrow = length(w_list), ncol = length(window_list),
                        dimnames = list(paste0("w=", w_list), paste0("window=", window_list)))

signal_type <- "XSMOM"

#For loop der tester for alle givet w'er og vinduer
for (i in seq_along(window_list)){
    window <- window_list[i]

  asset_names <- names(data_monthly)[2:50]
  weights <- data.frame(
    Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(BacktestDates), ncol = length(asset_names))),
      asset_names
    )
  )  
  for (j in seq_along(w_list)){
    w <- w_list[j]
      for (k in 1:(nrow(weights))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
        Current_date <- weights$Dates[k]  # ultimo måned t

        # 1. Data til signal og risiko
        #Her gemmes datoerne fra et år siden
        signal_data_monthly <- data_monthly_log %>%
            filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
            select(all_of(asset_names))
        
        risk_data_monthly <- data_monthly_log %>%
            filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
            select(all_of(asset_names))
        
        # 2. Find aktiver uden NA’er i begge vinduer
        valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
        valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
        active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
        
        # 3. Udregn signal, risikomodel og vægte
        signal <- XSMOM(Current_date, active_assets)

        risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde
        w_t <- anker_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
        
        # 4. Gem vægtene på datoen for næste måned
        weights[k, active_assets] <- w_t

        if(k %% 300 ==0){
            print(k)
            cat("out of: ")
            print(nrow(weights))
        }
      }
      
      #Gemmer det i en ny dataframe, for at opretholde "raw" udregninger
      #weightsmaster <- weights
      ######################################################
      #Laver dato rækken til dato format
      weights <- weights %>%
      mutate(Dates = as.Date(Dates))
      A <- weights
      names(A)[names(A) == "Dates"] <- "Date"
      #Finder mængden investeret i det riskiofrie aktiv
      
      A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
      A <- A %>% mutate(rf_weight = 0)
      #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
      B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
      #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
      AB <- left_join(A,B,by="Date") 
      AB <- AB %>%
          mutate(across(everything(), ~replace_na(., 0)))
      AB <- AB %>% rename(
      rf.x =rf_weight,
      rf.y = RF
      )
      Afkast <- AB %>% select(ends_with(".y"))
      Weights_test <- AB %>% select(ends_with(".x"))
      colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
      colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
      stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
      Results <- Afkast * Weights_test
      AB_final <- bind_cols(AB %>% select(Date), Results)
      AB_final <- AB_final %>%
        mutate(Afkast = rowSums(select(., -Date)))
      Afkast <- AB_final %>% select(Date, Afkast)

      sharpe_matrix[j, i] <- (mean(Afkast$Afkast)/sd(Afkast$Afkast))*sqrt(12)
      
      cat("For w = ", w, "\n")
      cat("For windue = ", window, "\n")
    }
}
################################################################
#1/sigma
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)

asset_names <- names(data_monthly)[2:50]
weights_vol <- data.frame(
  Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
  setNames(
    as.data.frame(matrix(NA, nrow = nrow(BacktestDates), ncol = length(asset_names))),
    asset_names
  )
)

for (k in 1:(nrow(weights_vol))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
  Current_date <- weights_vol$Dates[k]  # ultimo måned t

  # 1. Data til signal og risiko
  #Her gemmes datoerne fra et år siden
  vol_data_monthly <- data_monthly_log %>%
      filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
      select(all_of(asset_names))

  valid_vol_assets <- sapply(vol_data_monthly, function(x) sum(is.na(x)) == 0)
  vol_active_assets <- asset_names[valid_vol_assets]

  vol_t <- vol_data_monthly %>% summarise(across(everything(), ~sd(.x)))
  weights_vol[k, vol_active_assets]<-vol_t[vol_active_assets]      
}

cols <- names(weights_vol)[2:ncol(weights_vol)]

x <- as.numeric(unlist(weights_vol[i, cols]))


out <- matrix(0,
              nrow = nrow(weights_vol),
              ncol = length(cols),
              dimnames = list(NULL, cols))

# Fyld hver række ud
for (i in seq_len(nrow(weights_vol))) {
  x <- as.numeric(unlist(weights_vol[i, cols]))  # kun aktiver
  non_na <- !is.na(x)
  
  if (sum(non_na) > 0) {
    inv_vol <- 1 / x[non_na]
    weights <- inv_vol / sum(inv_vol)
    out[i, cols[non_na]] <- weights
  }
}

# Sæt det tilbage i weigths
weights_vol[ , cols] <- out

afkast_vol <- data_monthly_log %>% select(-RF)
afkast_vol <- afkast_vol %>%
    mutate(across(everything(), ~replace_na(., 0)))


# Antag: begge dataframes har kolonnen Date, og ellers helt ens kolonner
num_cols <- setdiff(names(ligevægt), "Date")

result <- ligevægt %>%
  # join kun de matchende datoer – ekstra datoer i data_mon bliver kasseret
  inner_join(afkast_vol, by = "Date", suffix = c("_l", "_m")) %>%
  # for hver .m-kolonne: gang med tilsvarende _l-kolonne
  mutate(across(
    ends_with("_m"),
    ~ .x * get(sub("_m$", "_l", cur_column()))
  )) %>%
  # behold kun Date + de nye produkt-kolonner (.m), og strip suffix
  select(Date, ends_with("_m")) %>%
  rename_with(~ sub("_m$", "", .x))


result <- result %>%
 mutate(Afkast = rowSums(select(., -Date)))

(mean(result$Afkast)/sd(result$Afkast))*sqrt(12)

afkast_ligevægt_monthly <- result %>% mutate(across(Afkast, ~(exp(.)-1))) %>% select(c(Date,Afkast))
#Laver afkast om til årligt afkast OBS. virker når afkast er i log
Afkast_Årligt <- result %>%
    mutate(Year = lubridate::year(Date)) %>%
    select(-Date) %>%
    group_by(Year) %>%
    summarise(across(everything(), ~ exp(sum(., na.rm = TRUE))-1)) %>%
    as.data.frame()

Afkast_Årligt <- Afkast_Årligt %>% select(Year,Afkast)

mean(Afkast_Årligt[,2])/sd(Afkast_Årligt[,2])

###########################################################################

################################################################
#1/N

###########################################################################
#Giver inpunts til rebalancerings portefølje
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)

ligevægt <- BacktestDates %>% select(-RF)

cols <- setdiff(names(ligevægt), "Date")

# Lav en matrix til output
out <- matrix(0,
              nrow = nrow(ligevægt),
              ncol = length(cols),
              dimnames = list(NULL, cols))


# Fyld hver række ud
for(i in seq_len(nrow(ligevægt))) {
  x <- ligevægt[i, cols]
  non_na <- !is.na(x)
  m_i <- sum(non_na)             # antal kolonner uden NA i række i
  if (m_i > 0) {
    out[i, non_na] <- 1 / m_i
  }
}

# Sæt det tilbage i ligevægt
ligevægt[ , cols] <- out

afkast_til_ligevægt <- data_monthly_log %>% select(-RF)
afkast_til_ligevægt <- afkast_til_ligevægt %>%
    mutate(across(everything(), ~replace_na(., 0)))


# Antag: begge dataframes har kolonnen Date, og ellers helt ens kolonner
num_cols <- setdiff(names(ligevægt), "Date")


A <- ligevægt 
#Finder mængden investeret i det riskiofrie aktiv
A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
A <- A %>% mutate(rf_weight = 0)
#A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
#B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
AB <- left_join(A,B,by="Date") 
AB <- AB %>%
    mutate(across(everything(), ~replace_na(., 0)))
AB <- AB %>% rename(
rf.x =rf_weight,
rf.y = RF
)
Afkast <- AB %>% select(ends_with(".y"))
Weights_test <- AB %>% select(ends_with(".x"))
colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
Results <- Afkast * Weights_test
AB_final <- bind_cols(AB %>% select(Date), Results)
AB_final <- AB_final %>%
  mutate(Afkast = rowSums(select(., -Date)))
Afkast <- AB_final %>% select(Date, Afkast)

(mean(Afkast$Afkast)/sd(Afkast$Afkast))*sqrt(12)

ligevægt_monthly_return <- Afkast


##################################################################
#--------OOS----------#
#Lavet så vinduet skal ændres for hver portefølje, i stedet for kopiering
#Giver inpunts til rebalancerings portefølje
StartofData <- as.Date("1927-01-01")
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
RunPeriod <- data_monthly_log %>% filter(Date <=EndBackTest & Date >= StartofData) %>% select(Date)


#liste over givet vinduer samt w'er der ønskes at teste for
window_list <-c(36,60,90,120)
w_list <- c(0,0.1,0.25,0.5,0.75,0.9,0.99,1)

w_names <- paste0("w_", w_list)

#Danner dataframe til at gemme SR for hver dato
SR_values_montly_X_36 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_X_60 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_X_90 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_X_120 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_T_36 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_T_60 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_T_90 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))
SR_values_montly_T_120 <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))

equity_list=c("SR_values_montly_X_36","SR_values_montly_X_60","SR_values_montly_X_90","SR_values_montly_X_120",
"SR_values_montly_T_36","SR_values_montly_T_60","SR_values_montly_T_90","SR_values_montly_T_120")

colnames(SR_values_montly_X_36)[-1] <- w_names
colnames(SR_values_montly_X_60)[-1] <- w_names
colnames(SR_values_montly_X_90)[-1] <- w_names
colnames(SR_values_montly_X_120)[-1] <- w_names
colnames(SR_values_montly_T_36)[-1] <- w_names
colnames(SR_values_montly_T_60)[-1] <- w_names
colnames(SR_values_montly_T_90)[-1] <- w_names
colnames(SR_values_montly_T_120)[-1] <- w_names

signal_type_list <- c("XSMOM","TSMOM")

#For loop der tester for alle givet w'er og vinduer

asset_names <- names(data_monthly)[2:50]

for(o in seq_along(signal_type_list)){

  signal_type <- signal_type_list[o]

  for(½ in seq_along(window_list)){

    window <- window_list[l]
    
    #vær sikker på rækkefølgen er rigtig
    eq_port <- switch(signal_type,
      "XSMOM" = switch(as.character(window),
        "36" =  SR_values_montly_X_36,
        "60" =  SR_values_montly_X_60,
        "90" =  SR_values_montly_X_90,
        "120" =  SR_values_montly_X_120
      ),
      "TSMOM" = switch(as.character(window),
        "36" =  SR_values_montly_T_36,
        "60" =  SR_values_montly_T_60,
        "90" =  SR_values_montly_T_90,
        "120" =  SR_values_montly_T_120
      )
    )
    for (j in seq_along(w_list)){
      w <- w_list[j]

      weights <- data.frame(
        Dates = RunPeriod[[1]],  # henter den ene kolonne som vector
        setNames(
          as.data.frame(matrix(NA, nrow = nrow(RunPeriod), ncol = length(asset_names))),
          asset_names
        )
      )  

      for (k in 1:(nrow(RunPeriod)-window)) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
        k <- k + window
        Current_date <- RunPeriod$Date[k]  # ultimo måned t

        # 1. Data til signal og risiko
        #Her gemmes datoerne fra et år siden
        signal_data_monthly <- data_monthly_log %>%
            filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
            select(all_of(asset_names))
        
        risk_data_monthly <- data_monthly_log %>%
            filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
            select(all_of(asset_names))
        
        # 2. Find aktiver uden NA’er i begge vinduer
        valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
        valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
        active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
        
        # 3. Udregn signal, risikomodel og vægte
        if (signal_type=="TSMOM"){
          signal <- TSMOM(Current_date, active_assets)
        } else if (signal_type=="XSMOM"){
          signal <- XSMOM(Current_date, active_assets)
        } else if (signal_type=="Col"){
          signal <- CMean(Current_date, active_assets)
        } else {
          print("Not acceptable signal")
        }
        risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde
        w_t <- simple_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
        
        # 4. Gem vægtene på datoen for næste måned
        weights[k, active_assets] <- w_t

        if(k %% 300 ==0){
            print(k)
            cat("out of: ")
            print(nrow(weights))
        }
      }

      ######################################################
      #Laver dato rækken til dato format
      weights <- weights %>%
      mutate(Dates = as.Date(Dates))

      weights <- weights %>% filter(Dates >= StartofData %m+% months(window)) 

      A <- weights
      names(A)[names(A) == "Dates"] <- "Date"
      #Finder mængden investeret i det riskiofrie aktiv
      
      A <- A  %>% mutate(across(-Date, ~replace_na(.,0)))
      A <- A %>% mutate(rf_weight = 0)
      #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
      B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartofData %m+% months(window))
      #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
      AB <- left_join(A,B,by="Date") 
      AB <- AB %>%
          mutate(across(-Date, ~replace_na(., 0)))
      AB <- AB %>% rename(
      rf.x =rf_weight,
      rf.y = RF
      )
      Afkast <- AB %>% select(ends_with(".y"))
      Weights_test <- AB %>% select(ends_with(".x"))
      colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
      colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
      stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
      Results <- Afkast * Weights_test
      AB_final <- bind_cols(AB %>% select(Date), Results)
      AB_final <- AB_final %>%
        mutate(Afkast = rowSums(select(., -Date)))
      Afkast <- AB_final %>% select(Date, Afkast)

      for(i in seq_len(nrow(eq_port))){
        SR_date <- eq_port$Date[i]
        Afkast_Upto <- Afkast %>% filter(Date >= StartofData & Date <= SR_date)
        SR <- mean(Afkast_Upto[,2])/sd(Afkast_Upto[,2])
        eq_port[i, paste0("w_", w)] <- SR
      }

      cat("For w = ", w, "\n")
      cat("For windue = ", window, "\n")
      cat("For signal = ", signal_type, "\n")
    }
    eq_port <- eq_port %>%
      rowwise() %>% mutate(Best_w = {
          max_col <- names(across(starts_with("w_")))[which.max(c_across(starts_with("w_")))]
          as.numeric(str_remove(max_col, "w_"))
        }
      ) %>% ungroup()

    eq_name <- switch(signal_type,
      "XSMOM" = paste0("SR_values_montly_X_", window),
      "TSMOM" = paste0("SR_values_montly_T_", window)
    )
    assign(eq_name, eq_port, envir = .GlobalEnv)
  }
}

########################################################
#OOS fortsat - indsæt de forskellige w'er til datoerne i hver portefølje

theta <- 0.05

#Data frame til OOS resultater
OOS <- data.frame(eq1=numeric(),eq2=numeric(),eq3=numeric(),eq4=numeric(),eq5=numeric(),eq6=numeric(),eq7=numeric(),eq8=numeric())
OOS_names <- names(OOS)

vægte_data <- data.frame(sum_positiv=numeric(),sum_negativ=numeric(),sum_absolut=numeric(),average_vol=numeric(),average_max_positiv=numeric(),average_max_negativ=numeric(),average_diff_sums=numeric())

for (i in seq_along(equity_list)){
  window <- switch(equity_list[i],
  "SR_values_montly_X_36" = 36,
  "SR_values_montly_X_60" = 60,
  "SR_values_montly_X_90" = 90,
  "SR_values_montly_X_120" = 120,
  "SR_values_montly_T_36" = 36,
  "SR_values_montly_T_60" = 60,
  "SR_values_montly_T_90" = 90,
  "SR_values_montly_T_120" = 120
  )

  asset_names <- names(data_monthly)[2:50]
  weights <- data.frame(
    Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(BacktestDates), ncol = length(asset_names))),
      asset_names
    )
  )  
  for (k in 1:(nrow(weights))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
    Current_date <- weights$Dates[k]  # ultimo måned t

    # 1. Data til signal og risiko
    #Her gemmes datoerne fra et år siden
    signal_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
        select(all_of(asset_names))
    
    risk_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
        select(all_of(asset_names))
    
    # 2. Find aktiver uden NA’er i begge vinduer
    valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
    valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
    active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
    
    # 3. Udregn signal, risikomodel og vægte
    if (i <= 4){
      signal <- XSMOM(Current_date, active_assets)
    } else {
      signal <- TSMOM(Current_date, active_assets)
    }
    w <- switch(equity_list[i],
    "SR_values_montly_X_36" = as.numeric(SR_values_montly_X_36[k,10]),
    "SR_values_montly_X_60" = as.numeric(SR_values_montly_X_60[k,10]),
    "SR_values_montly_X_90" = as.numeric(SR_values_montly_X_90[k,10]),
    "SR_values_montly_X_120" = as.numeric(SR_values_montly_X_120[k,10]),
    "SR_values_montly_T_36" = as.numeric(SR_values_montly_T_36[k,10]),
    "SR_values_montly_T_60" = as.numeric(SR_values_montly_T_60[k,10]),
    "SR_values_montly_T_90" = as.numeric(SR_values_montly_T_90[k,10]),
    "SR_values_montly_T_120" = as.numeric(SR_values_montly_T_120[k,10])  
    )
    risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde
    w_t <- simple_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
      
      # 4. Gem vægtene på datoen for næste måned
      weights[k, active_assets] <- w_t

      if(k %% 300 ==0){
          print(k)
          cat("out of: ")
          print(nrow(weights))
      }
    }
    
      #Gemmer det i en ny dataframe, for at opretholde "raw" udregninger
      #weightsmaster <- weights
      ######################################################
      #Laver dato rækken til dato format
      weights <- weights %>%
      mutate(Dates = as.Date(Dates))
      A <- weights
      names(A)[names(A) == "Dates"] <- "Date"
      #Finder mængden investeret i det riskiofrie aktiv
      
      A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
      A <- A %>% mutate(rf_weight = 0)
      #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
      B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
      #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
      AB <- left_join(A,B,by="Date") 
      AB <- AB %>%
          mutate(across(everything(), ~replace_na(., 0)))
      AB <- AB %>% rename(
      rf.x =rf_weight,
      rf.y = RF
      )
      Afkast <- AB %>% select(ends_with(".y"))
      Weights_test <- AB %>% select(ends_with(".x"))
      colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
      colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
      stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
      Results <- Afkast * Weights_test
      AB_final <- bind_cols(AB %>% select(Date), Results)
      AB_final <- AB_final %>%
        mutate(Afkast = rowSums(select(., -Date)))
      Afkast <- AB_final %>% select(Date, Afkast)

      OOS[1,i] <- (mean(Afkast$Afkast)/sd(Afkast$Afkast))*sqrt(12)
      
      cat("For w = ", w, "\n")
      cat("For windue = ", window, "\n")
  }

######################################################################################
#OOS anker
StartofData <- as.Date("1927-01-01")
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
RunPeriod <- data_monthly_log %>% filter(Date <=EndBackTest & Date >= StartofData) %>% select(Date)


#liste over givet vinduer samt w'er der ønskes at teste for
window_list <-c(60)
w_list <- c(0,0.1,0.25,0.5,0.75,0.9,0.99,1)

w_names <- paste0("w_", w_list)

#Danner dataframe til at gemme SR for hver dato
SR_values_montly_anker <- data.frame(Date= BacktestDates$Date, matrix(NA, nrow = length(BacktestDates$Date), ncol = length(w_list)))

colnames(SR_values_montly_anker)[-1] <- w_names

asset_names <- names(data_monthly)[2:50]
for (j in seq_along(w_list)){
  w <- w_list[j]

  weights <- data.frame(
    Dates = RunPeriod[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(RunPeriod), ncol = length(asset_names))),
      asset_names
    )
  )  

  for (k in 1:(nrow(RunPeriod)-window)) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
    k <- k + window
    Current_date <- RunPeriod$Date[k]  # ultimo måned t

    # 1. Data til signal og risiko
    #Her gemmes datoerne fra et år siden
    signal_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
        select(all_of(asset_names))
    
    risk_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
        select(all_of(asset_names))
    
    # 2. Find aktiver uden NA’er i begge vinduer
    valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
    valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
    active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
    
    # 3. Udregn signal, risikomodel og vægte
    signal <- XSMOM(Current_date, active_assets)
    risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde
    w_t <- anker_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
    
    # 4. Gem vægtene på datoen for næste måned
    weights[k, active_assets] <- w_t

    if(k %% 300 ==0){
        print(k)
        cat("out of: ")
        print(nrow(weights))
    }
  }

  ######################################################
  #Laver dato rækken til dato format
  weights <- weights %>%
  mutate(Dates = as.Date(Dates))

  weights <- weights %>% filter(Dates >= StartofData %m+% months(window)) 

  A <- weights
  names(A)[names(A) == "Dates"] <- "Date"
  #Finder mængden investeret i det riskiofrie aktiv
  
  A <- A  %>% mutate(across(-Date, ~replace_na(.,0)))
  A <- A %>% mutate(rf_weight = 0)
  #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
  B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartofData %m+% months(window))
  #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
  AB <- left_join(A,B,by="Date") 
  AB <- AB %>%
      mutate(across(-Date, ~replace_na(., 0)))
  AB <- AB %>% rename(
  rf.x =rf_weight,
  rf.y = RF
  )
  Afkast <- AB %>% select(ends_with(".y"))
  Weights_test <- AB %>% select(ends_with(".x"))
  colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
  colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
  stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
  Results <- Afkast * Weights_test
  AB_final <- bind_cols(AB %>% select(Date), Results)
  AB_final <- AB_final %>%
    mutate(Afkast = rowSums(select(., -Date)))
  Afkast <- AB_final %>% select(Date, Afkast)

  for(i in seq_len(nrow(SR_values_montly_anker))){
    SR_date <- SR_values_montly_anker$Date[i]
    Afkast_Upto <- Afkast %>% filter(Date >= StartofData & Date <= SR_date)
    SR <- mean(Afkast_Upto[,2])/sd(Afkast_Upto[,2])
    SR_values_montly_anker[i, paste0("w_", w)] <- SR
  }

  cat("For w = ", w, "\n")
  cat("For windue = ", window, "\n")
}

SR_values_montly_anker <- SR_values_montly_anker %>%
  rowwise() %>% mutate(Best_w = {
      max_col <- names(across(starts_with("w_")))[which.max(c_across(starts_with("w_")))]
      as.numeric(str_remove(max_col, "w_"))
    }
  ) %>% ungroup()

#anker Forsat
###########################################################################
#Giver inpunts til rebalancerings portefølje
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)

#liste over givet vinduer samt w'er der ønskes at teste for
window_list <- c(60)

#Matrix til SR værdier
sharpe_matrix <- matrix(NA, nrow = length(w_list), ncol = length(window_list),
                        dimnames = list(paste0("w=", w_list), paste0("window=", window_list)))

signal_type <- "XSMOM"


asset_names <- names(data_monthly)[2:50]
weights <- data.frame(
  Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
  setNames(
    as.data.frame(matrix(NA, nrow = nrow(BacktestDates), ncol = length(asset_names))),
    asset_names
  )
)
for (k in 1:(nrow(weights))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
  Current_date <- weights$Dates[k]  # ultimo måned t
  w <- as.numeric(SR_values_montly_anker[k,10])
  
  # 1. Data til signal og risiko
  #Her gemmes datoerne fra et år siden
  signal_data_monthly <- data_monthly_log %>%
      filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
      select(all_of(asset_names))
  
  risk_data_monthly <- data_monthly_log %>%
      filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
      select(all_of(asset_names))
  
  # 2. Find aktiver uden NA’er i begge vinduer
  valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
  valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
  active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
  
  # 3. Udregn signal, risikomodel og vægte
  signal <- XSMOM(Current_date, active_assets)

  risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde
  w_t <- anker_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window)
  
  # 4. Gem vægtene på datoen for næste måned
  weights[k, active_assets] <- w_t

  if(k %% 300 ==0){
      print(k)
      cat("out of: ")
      print(nrow(weights))
  }
}

#Gemmer det i en ny dataframe, for at opretholde "raw" udregninger
#weightsmaster <- weights
######################################################
#Laver dato rækken til dato format
weights <- weights %>%
mutate(Dates = as.Date(Dates))
A <- weights
names(A)[names(A) == "Dates"] <- "Date"
#Finder mængden investeret i det riskiofrie aktiv

A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
A <- A %>% mutate(rf_weight = 0)
#A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
B <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)
#B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
AB <- left_join(A,B,by="Date") 
AB <- AB %>%
    mutate(across(everything(), ~replace_na(., 0)))
AB <- AB %>% rename(
rf.x =rf_weight,
rf.y = RF
)
Afkast <- AB %>% select(ends_with(".y"))
Weights_test <- AB %>% select(ends_with(".x"))
colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
Results <- Afkast * Weights_test
AB_final <- bind_cols(AB %>% select(Date), Results)
AB_final <- AB_final %>%
  mutate(Afkast = rowSums(select(., -Date)))
Afkast <- AB_final %>% select(Date, Afkast)

pf9_monthly_simpel <- Afkast %>% mutate(across(Afkast, ~exp(.)-1))
#Laver afkast om til årligt afkast OBS. virker når afkast er i log

(mean(Afkast$Afkast)/sd(Afkast$Afkast))*sqrt(12)

cat("For w = ", w, "\n")
cat("For windue = ", window, "\n")


#############################################################################
#Plot egenværdi
#Indsæt værdier til risiko model
window <- 120
theta <- 0.0
gamma <- 1
w <- 0.25

###########################################################################
#Giver inpunts til rebalancerings portefølje
StartBackTest <- as.Date("1942-01-01")
EndBackTest <- as.Date("2018-12-31")
BacktestDates <- data_monthly_log %>% filter(Date <= EndBackTest & Date >= StartBackTest)


#Danner dataframe til at gemme SR samt den laveste egenværdi til et givet vindue
#SR_daglig <- data.frame(w=numeric(),Sharpe =numeric())
#SR_årlig_ex <- data.frame(w=numeric(),window=numeric(),Sharpe =numeric())
#SR_årlig <- data.frame(w=numeric(),window=numeric(),Sharpe =numeric())
LowD <- data.frame(window=numeric(),DV=numeric(), MaxDiffD= numeric())
LowDtilde <- data.frame(window=numeric(),DtildeV=numeric(), MaxDiffDtilde = numeric())

#liste over givet vinduer samt w'er der ønskes at teste for
window_list <- seq(30,120, by = 1 )
w_list <- c(0)

#Matrix til SR værdier
sharpe_matrix <- matrix(NA, nrow = length(w_list), ncol = length(window_list),
                        dimnames = list(paste0("w=", w_list), paste0("window=", window_list)))

signal_type <- "XSMOM"

#For loop der tester for alle givet w'er og vinduer
for (i in seq_along(window_list)){
    window <- window_list[i]

  asset_names <- names(data_monthly)[2:50]
  weights <- data.frame(
    Dates = BacktestDates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(BacktestDates), ncol = length(asset_names))),
      asset_names
    )
  )  
    #Sætter en ny egenv, for at slette den gamle, skal være høj så den ikke påvirker resultatet
  egenD <- 5000
  egenDtilde <- 5000
  MaxDiffD <- 0
  MaxDiffDtilde <- 0
  # Finder den laveste egeneværdi i vinduet
  for (i in 1:(nrow(weights))){
      Current_date <- weights$Dates[i] 
      # 1. Data til signal og risiko
      #Her gemmes datoerne fra et år siden
      signal_data_monthly <- data_monthly %>%
          filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
          select(all_of(asset_names))
      
      risk_data_monthly <- data_monthly %>%
          filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
          select(all_of(asset_names))
      
      # 2. Find aktiver uden NA’er i begge vinduer
      valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
      valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
      active_assets <- asset_names[valid_signal_assets & valid_risk_assets]

      #Opdatere den laveste egenværdi fundet
      egenD <- min(egenD, Risk_model_monthly(Current_date, window, theta, active_assets)$lowD)
      egenDtilde <- min(egenDtilde, Risk_model_monthly(Current_date, window, theta, active_assets)$lowDtilde)

      #Total af antal af aktive aktiver over alle periode
      MaxDiffD <- max(MaxDiffD, abs(Risk_model_monthly(Current_date, window, theta, active_assets)$MaxDiffD))
      MaxDiffDtilde <- max(MaxdiffDtilde, abs(Risk_model_monthly(Current_date, window, theta, active_assets)$MaxDiffDtilde))

    }
    LowD <- rbind(LowD, data.frame(window=window, DV=egenD, MaxDiffD = MaxDiffD))
    LowDtilde <- rbind(LowDtilde, data.frame(window=window, DtildeV=egenDtilde, MaxDiffDtilde = MaxDiffDtilde))
    cat("kørt for ",window , "\n")
}

View(sharpe_matrix)

###############################################################
#Plot egenværdier
ggplot(LowD, aes(x = window, y = DV)) +
  geom_line(linewidth = 1) +    
  geom_point(size = 2) +
  labs(title = "Egenværdier",
       x = "Window",
       y = "Egenværdi") +
  theme_minimal() +
  theme(
    axis.text = element_text(size = 16, color = "black"),
    axis.title = element_text(size = 18, face = "bold"),
    plot.title = element_text(size = 20, face = "bold", hjust = 0.5),
    panel.grid.major = element_line(color = "gray80"), 
    axis.line = element_line(linewidth = 1, colour = "black")
  )

#med theta
ggplot(LowDtilde) +
geom_line(aes(x = window, y = DtildeV)) +
geom_line(aes(x = window, y = MaxDiffDtilde)) +     
geom_point(size = 2) +
labs(title = "Egenværdier",
      x = "Window",
      y = "Egenværdi") +
theme_minimal() +
theme(
  axis.text = element_text(size = 16, color = "black"),
  axis.title = element_text(size = 18, face = "bold"),
  plot.title = element_text(size = 20, face = "bold", hjust = 0.5),
  panel.grid.major = element_line(color = "gray80"), 
  axis.line = element_line(linewidth = 1, colour = "black")
)

###############################################################
#FF - Faktor
Start_Date_FF_Factor <- "1963-07-01"
End_Date_FF_Factor <- "2018-12-31"
FF_Factor_dates <- data_monthly_log %>% filter(Date <= End_Date_FF_Factor & Date >= Start_Date_FF_Factor)

#Date frame til hvert afkast
afkast_montly_X_36 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_X_60 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_X_90 <- data.frame(Date= BacktestDates$Date, mafkast = numeric())
afkast_montly_X_120 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_T_36 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_T_60 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_T_90 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_T_120 <- data.frame(Date= BacktestDates$Date, afkast = numeric())
afkast_montly_X_anker <- data.frame(Date= BacktestDates$Date, afkast = numeric())

FF_5_faktor <- read.csv("C:/Users/nikol/OneDrive - CBS - Copenhagen Business School/Bachelor/Data/FF_5_factor.csv", header = TRUE, sep=",")
FF_5_faktor <- FF_5_faktor %>% select(-RF)
FF_5_faktor$Date <- as.Date(paste0(FF_5_faktor$Date, "01"), format = "%Y%m%d")
FF_5_faktor <- FF_5_faktor %>% filter(Date >= Start_Date_FF_Factor & Date <= End_Date_FF_Factor)

#Data frame til SR FF
SR_FF_5_faktor <- data.frame(Mkt.RF_SR = numeric(), SMB_SR = numeric(), HML_SR = numeric(), RMW_SR = numeric(), CMA_SR = numeric())

for(i in seq_along(SR_FF_5_faktor)){
  temp_data <- FF_5_faktor %>%
    mutate(Year = lubridate::year(Date)) %>%
    select(-Date) %>%
    group_by(Year) %>%
    reframe(across(everything(), ~ (. / 100))) %>%
    as.data.frame()
  SR_FF_5_faktor[1,i] <- (mean(temp_data[,i+1])*12)/(sd(temp_data[ ,i+1])*sqrt(12))
}

#--------------FF-reg--------------------#

#List til afkast navne
Afkast_data_frame <- c("afkast_montly_X_36","afkast_montly_X_60", "afkast_montly_X_90", "afkast_montly_X_120", "afkast_montly_T_36","afkast_montly_T_60", "afkast_montly_T_90", "afkast_montly_T_120", "afkast_montly_X_anker")

for (i in seq_along(Afkast_data_frame)){
  window <- switch(Afkast_data_frame[i],
  "afkast_montly_X_36" = 36,
  "afkast_montly_X_60" = 60,
  "afkast_montly_X_90" = 90,
  "afkast_montly_X_120" = 120,
  "afkast_montly_T_36" = 36,
  "afkast_montly_T_60" = 60,
  "afkast_montly_T_90" = 90,
  "afkast_montly_T_120" = 120,
  "afkast_montly_X_anker" = 60
  )

  asset_names <- names(data_monthly)[2:50]
  weights <- data.frame(
    Dates = FF_Factor_dates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(FF_Factor_dates), ncol = length(asset_names))),
      asset_names
    )
  )  
  for (k in 1:(nrow(weights))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
    Current_date <- weights$Dates[k]  # ultimo måned t

    # 1. Data til signal og risiko
    #Her gemmes datoerne fra et år siden
    signal_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
        select(all_of(asset_names))
    
    risk_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
        select(all_of(asset_names))
    
    # 2. Find aktiver uden NA’er i begge vinduer
    valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
    valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
    active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
    
    # 3. Udregn signal, risikomodel og vægte
    if (i <= 4){
      signal <- XSMOM(Current_date, active_assets)
    } else if (i<=8)  {
      signal <- TSMOM(Current_date, active_assets)
    } else{
      signal <- XSMOM(Current_date, active_assets)
    }

    #For at datoerne passer
    k <- k + 258
    
    w <- switch(as.character(Afkast_data_frame[i]),
    "afkast_montly_X_36" = as.numeric(SR_values_montly_X_36[k,10]),
    "afkast_montly_X_60" = as.numeric(SR_values_montly_X_60[k,10]),
    "afkast_montly_X_90" = as.numeric(SR_values_montly_X_90[k,10]),
    "afkast_montly_X_120" = as.numeric(SR_values_montly_X_120[k,10]),
    "afkast_montly_T_36" = as.numeric(SR_values_montly_T_36[k,10]),
    "afkast_montly_T_60" = as.numeric(SR_values_montly_T_60[k,10]),
    "afkast_montly_T_90" = as.numeric(SR_values_montly_T_90[k,10]),
    "afkast_montly_T_120" = as.numeric(SR_values_montly_T_120[k,10]),
    "afkast_montly_X_anker" = as.numeric(SR_values_montly_anker[k,10])
    )

    risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde

    if(Afkast_data_frame[i]=="afkast_montly_X_anker"){
      w_t <- anker_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
    } else {
      w_t <- simple_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
    }

    #Tilpasser k
    k <- k - 258
      # 4. Gem vægtene på datoen for næste måned
      weights[k, active_assets] <- w_t

      if(k %% 300 ==0){
          print(k)
          cat("out of: ")
          print(nrow(weights))
      }
    }
    
      #Gemmer det i en ny dataframe, for at opretholde "raw" udregninger
      #weightsmaster <- weights
      ######################################################
      #Laver dato rækken til dato format
      weights <- weights %>%
      mutate(Dates = as.Date(Dates))
      A <- weights
      names(A)[names(A) == "Dates"] <- "Date"
      #Finder mængden investeret i det riskiofrie aktiv
      
      A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
      A <- A %>% mutate(rf_weight = 0)
      #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
      B <- data_monthly_log %>% filter(Date <= End_Date_FF_Factor & Date >= Start_Date_FF_Factor)
      #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
      AB <- left_join(A,B,by="Date") 
      AB <- AB %>%
          mutate(across(everything(), ~replace_na(., 0)))
      AB <- AB %>% rename(
      rf.x =rf_weight,
      rf.y = RF
      )
      Afkast <- AB %>% select(ends_with(".y"))
      Weights_test <- AB %>% select(ends_with(".x"))
      colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
      colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
      stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
      Results <- Afkast * Weights_test
      AB_final <- bind_cols(AB %>% select(Date), Results)
      AB_final <- AB_final %>%
        mutate(Afkast = rowSums(select(., -Date)))
      Afkast <- AB_final %>% select(Date, Afkast)

      assign(paste0(Afkast_data_frame[[i]]), Afkast, envir = .GlobalEnv)
         
      cat("For w = ", w, "\n")
      cat("For windue = ", window, "\n")
 }

afkast_INDMOM_FF <- afkast_INDMOM %>% filter(Date >= date(Start_Date_FF_Factor))

scale_vol_10 <- function(r) {
  ann_sd <- sd(r, na.rm = TRUE) * sqrt(12)
  scaled_r <- r * (0.1 / ann_sd)
  return(scaled_r)
}

#Sikre FF i simpel afkast
FF_5_faktor_simpel_monthly <- FF_5_faktor %>% mutate(across(-Date, ~./100))


MktRF <- FF_5_faktor$Mkt.RF
SMB <- FF_5_faktor$SMB
HML <- FF_5_faktor$HML
RMW <- FF_5_faktor$RMW
CMA <- FF_5_faktor$CMA

MktRF_scaled <- scale_vol_10(MktRF)
SMB_scaled <- scale_vol_10(SMB)
HML_scaled <- scale_vol_10(HML)
RMW_scaled <- scale_vol_10(RMW)
CMA_scaled <- scale_vol_10(CMA)

afkast_scaled_X_36 <- scale_vol_10(afkast_montly_X_36$Afkast)
afkast_scaled_X_60 <- scale_vol_10(afkast_montly_X_60$Afkast)
afkast_scaled_X_90 <- scale_vol_10(afkast_montly_X_90$Afkast)
afkast_scaled_X_120 <- scale_vol_10(afkast_montly_X_120$Afkast)

afkast_scaled_T_60 <- scale_vol_10(afkast_montly_T_36$Afkast)
afkast_scaled_T_36 <- scale_vol_10(afkast_montly_T_60$Afkast)
afkast_scaled_T_90 <- scale_vol_10(afkast_montly_T_90$Afkast)
afkast_scaled_T_120 <- scale_vol_10(afkast_montly_T_120$Afkast)

afkast_scaled_X_anker <- scale_vol_10(afkast_montly_X_anker$Afkast)


afkast_n <- afkast_ligevægt_monthly %>% filter(Date >= Start_Date_FF_Factor)
afkast_scaled_N <- scale_vol_10(afkast_n$Afkast)

INDMOM_scaled <- scale_vol_10(afkast_INDMOM_FF$Afkast)

eq1_FF_reg <- lm(afkast_scaled_X_36 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq1_FF_reg)

eq2_FF_reg <- lm(afkast_scaled_X_60 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq2_FF_reg)

eq3_FF_reg <- lm(afkast_scaled_X_90 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq3_FF_reg)

eq4_FF_reg <- lm(afkast_scaled_X_120 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq4_FF_reg)

eq5_FF_reg <- lm(afkast_scaled_T_36 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq5_FF_reg)

eq6_FF_reg <- lm(afkast_scaled_T_60 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq6_FF_reg)

eq7_FF_reg <- lm(afkast_scaled_T_90 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq7_FF_reg)

eq8_FF_reg <- lm(afkast_scaled_T_120 ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq8_FF_reg)

eq9_FF_reg <- lm(afkast_scaled_X_anker ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + RMW_scaled + CMA_scaled)
summary(eq9_FF_reg)

eqn_FF_reg <- lm(afkast_scaled_N ~ INDMOM_scaled + MktRF_scaled + SMB_scaled + HML_scaled + RMW_scaled + CMA_scaled)
summary(eqn_FF_reg)


#----Reg fortsat med 1/N fremfor Mkt-Rf----#

ligevægt_monthly_afkast_trimmed_FF <- ligevægt_monthly_afkast %>% filter(Date >= "1963-07-01")
ligevægt_scaled <- scale_vol_10(ligevægt_monthly_afkast_trimmed_FF$Afkast)


eq1_FF_reg <- lm(afkast_scaled_X_36 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq1_FF_reg)

eq2_FF_reg <- lm(afkast_scaled_X_60 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq2_FF_reg)

eq3_FF_reg <- lm(afkast_scaled_X_90 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq3_FF_reg)

eq4_FF_reg <- lm(afkast_scaled_X_120 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq4_FF_reg)

eq5_FF_reg <- lm(afkast_scaled_T_36 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq5_FF_reg)

eq6_FF_reg <- lm(afkast_scaled_T_60 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq6_FF_reg)

eq7_FF_reg <- lm(afkast_scaled_T_90 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq7_FF_reg)

eq8_FF_reg <- lm(afkast_scaled_T_120 ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + CMA_scaled + RMW_scaled)
summary(eq8_FF_reg)

eq9_FF_reg <- lm(afkast_scaled_X_anker ~ INDMOM_scaled + ligevægt_scaled + SMB_scaled + HML_scaled + RMW_scaled + CMA_scaled)
summary(eq9_FF_reg)






################################################################################
#---------------------------Devlop in afkast---------------------------------#
Start_Date_acc_return <- "1942-01-01"
End_Date_acc_return <- "2018-12-31"
acc_return_dates <- data_monthly_log %>% filter(Date <= End_Date_acc_return & Date >= Start_Date_acc_return)

#Date frame til hvert afkast
acc_afkast_montly_X_60 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_X_36 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_X_90 <- data.frame(Date= acc_return_dates$Date, mafkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_X_120 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_T_36 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_T_60 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_T_90 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_T_120 <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))
acc_afkast_montly_X_anker <- data.frame(Date= acc_return_dates$Date, afkast = numeric(length(acc_return_dates$Date)))

#List til afkast navne
acc_Afkast_data_frame <- c("acc_afkast_montly_X_36","acc_afkast_montly_X_60", "acc_afkast_montly_X_90", "acc_afkast_montly_X_120", "acc_afkast_montly_T_36","acc_afkast_montly_T_60", "acc_afkast_montly_T_90", "acc_afkast_montly_T_120", "acc_afkast_montly_X_anker")

for (i in seq_along(acc_Afkast_data_frame)){
  window <- switch(acc_Afkast_data_frame[i],
  "acc_afkast_montly_X_36" = 36,
  "acc_afkast_montly_X_60" = 60,
  "acc_afkast_montly_X_90" = 90,
  "acc_afkast_montly_X_120" = 120,
  "acc_afkast_montly_T_36" = 36,
  "acc_afkast_montly_T_60" = 60,
  "acc_afkast_montly_T_90" = 90,
  "acc_afkast_montly_T_120" = 120,
  "acc_afkast_montly_X_anker" = 60
  )

  asset_names <- names(data_monthly)[2:50]
  weights_acc_return <- data.frame(
    Dates = acc_return_dates[[1]],  # henter den ene kolonne som vector
    setNames(
      as.data.frame(matrix(NA, nrow = nrow(acc_return_dates), ncol = length(asset_names))),
      asset_names
    )
  )  
  for (k in 1:(nrow(weights_acc_return))) {  # bemærk: -1 for at kunne bruge [k+1] til næste måned
    Current_date <- weights_acc_return$Dates[k]  # ultimo måned t

    # 1. Data til signal og risiko
    #Her gemmes datoerne fra et år siden
    signal_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% years(1)) %>%
        select(all_of(asset_names))
    
    risk_data_monthly <- data_monthly_log %>%
        filter(Date < Current_date & Date >= Current_date %m-% months(window)) %>%
        select(all_of(asset_names))
    
    # 2. Find aktiver uden NA’er i begge vinduer
    valid_signal_assets <- sapply(signal_data_monthly, function(x) sum(is.na(x)) == 0)
    valid_risk_assets <- sapply(risk_data_monthly, function(x) sum(is.na(x)) == 0)
    active_assets <- asset_names[valid_signal_assets & valid_risk_assets]
    
    # 3. Udregn signal, risikomodel og vægte
    if (i <= 4){
      signal <- XSMOM(Current_date, active_assets)
    } else if (i<=8)  {
      signal <- TSMOM(Current_date, active_assets)
    } else{
      signal <- XSMOM(Current_date, active_assets)
    }
    
    w <- switch(as.character(acc_Afkast_data_frame[i]),
    "acc_afkast_montly_X_36" = as.numeric(SR_values_montly_X_36[k,10]),
    "acc_afkast_montly_X_60" = as.numeric(SR_values_montly_X_60[k,10]),
    "acc_afkast_montly_X_90" = as.numeric(SR_values_montly_X_90[k,10]),
    "acc_afkast_montly_X_120" = as.numeric(SR_values_montly_X_120[k,10]),
    "acc_afkast_montly_T_36" = as.numeric(SR_values_montly_T_36[k,10]),
    "acc_afkast_montly_T_60" = as.numeric(SR_values_montly_T_60[k,10]),
    "acc_afkast_montly_T_90" = as.numeric(SR_values_montly_T_90[k,10]),
    "acc_afkast_montly_T_120" = as.numeric(SR_values_montly_T_120[k,10]),
    "acc_afkast_montly_X_anker" = as.numeric(SR_values_montly_anker[k,10])
    )

    risk <- Risk_model_monthly(Current_date, window, theta, active_assets)$Sigmatilde

    if(acc_Afkast_data_frame[i]=="acc_afkast_montly_X_anker"){
      w_t <- anker_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
    } else {
      w_t <- simple_EPO(Current_date, signal, risk, gamma, w, window, active_assets, window_list[i])
    }

      # 4. Gem vægtene på datoen for næste måned
      weights_acc_return[k, active_assets] <- w_t

      if(k %% 300 ==0){
          print(k)
          cat("out of: ")
          print(nrow(weights_acc_return))
      }
    }
    
      #Gemmer det i en ny dataframe, for at opretholde "raw" udregninger
      #weightsmaster <- weights
      ######################################################
      #Laver dato rækken til dato format
      weights_acc_return <- weights_acc_return %>%
      mutate(Dates = as.Date(Dates))
      A <- weights_acc_return
      names(A)[names(A) == "Dates"] <- "Date"
      #Finder mængden investeret i det riskiofrie aktiv
      
      A <- A %>% mutate(across(everything(), ~replace_na(.,0)))
      A <- A %>% mutate(rf_weight = 0)
      #A <- A %>% mutate(rf_weight = 1 - rowSums(select(., -Date)))
      B <- data_monthly_log %>% filter(Date <= End_Date_acc_return & Date >= Start_Date_acc_return)
      #B <- data_monthly %>% mutate(across(-c(Date, RF), ~ (-RF)))
      AB <- left_join(A,B,by="Date") 
      AB <- AB %>%
          mutate(across(everything(), ~replace_na(., 0)))
      AB <- AB %>% rename(
      rf.x =rf_weight,
      rf.y = RF
      )
      Afkast <- AB %>% select(ends_with(".y"))
      Weights_test <- AB %>% select(ends_with(".x"))
      colnames(Afkast) <- gsub("\\.y$", "", colnames(Afkast))
      colnames(Weights_test) <- gsub("\\.x$", "", colnames(Weights_test))
      stopifnot(all(colnames(Afkast) == colnames(Weights_test)))
      Results <- Afkast * Weights_test
      AB_final <- bind_cols(AB %>% select(Date), Results)
      AB_final <- AB_final %>%
        mutate(Afkast = rowSums(select(., -Date)))
      Afkast <- AB_final %>% select(Date, Afkast)

      assign(paste0(acc_Afkast_data_frame[[i]]), Afkast, envir = .GlobalEnv)

      
      cat("For w = ", w, "\n")
      cat("For windue = ", window, "\n")
  }

acc_resultater <- lapply(acc_Afkast_data_frame, function(df_name) {
  df <- get(df_name)
  
  df %>%
    mutate(Year = lubridate::year(Date)) %>%      # ← Tilføjer år ud fra Date
    group_by(Year) %>%
    summarise(
      Afkast_år = (sum(Afkast, na.rm = TRUE)),
      .groups = "drop"
    ) %>%
    arrange(Year) %>%
    mutate(
      Akk_afkast = sum(Afkast_år),
      Portefølje = df_name
    ) %>%
    select(Year, Akk_afkast, Portefølje)
})

# Saml alle
acc_samlet <- bind_rows(acc_resultater)

# Pivotér til bredt format: én kolonne pr. portefølje
acc_bred <- acc_samlet %>%
  pivot_wider(
    names_from = Portefølje,
    values_from = Akk_afkast
  )                

colnames(acc_bred) <- c("Year", paste0("Pf", 1:9))

acc_lang <- acc_bred %>%
  pivot_longer(cols = -Year, names_to = "Portefølje", values_to = "Afkast_pct")

ggplot(acc_lang, aes(x = Year, y = Afkast_pct, color = Portefølje)) +
  geom_line(size = 1) +
  labs(
    title = "Kumulativ afkastudvikling (%)",
    x = "År",
    y = "Akkumuleret afkast (%)"
  ) +
  theme_minimal() +
  theme(
    text = element_text(size = 14),            # Gør al tekst større
    axis.title = element_text(size = 16),      # Aksetitler
    axis.text = element_text(size = 13),       # Akseværdier
    legend.text = element_text(size = 12),     # Legend
    legend.title = element_text(size = 13),
    plot.title = element_text(size = 18, face = "bold"),
    legend.position = "bottom"
  )

sp500_data <- read.csv("C:/Users/nikol/OneDrive - CBS - Copenhagen Business School/Bachelor/Data/S&P.csv", header = TRUE, sep=",")

sp500_prepared <- sp500_data %>%
  filter(Year >= 1942 & Year <= 2018) %>%
  mutate(
    Afkast = Afkast / 100,  # Konverter til decimal
    Akk_afkast = cumprod(1 + Afkast) - 1,
    Akk_afkast_pct = Akk_afkast * 100
  ) %>%
  select(Year, Akk_afkast_pct)

acc_bred <- acc_bred %>%
  left_join(sp500_prepared, by = "Year") %>%
  rename(SP500 = Akk_afkast_pct)


acc_lang <- acc_bred %>%
  pivot_longer(cols = -Year, names_to = "Portefølje", values_to = "Afkast_pct")

ggplot(acc_lang, aes(x = Year, y = Afkast_pct, color = Portefølje)) +
  geom_line(size = 1) +
  labs(
    title = "Kumulativ afkastudvikling (%)",
    x = "År",
    y = "Akkumuleret afkast (%)"
  ) +
  theme_minimal() +
  theme(
    text = element_text(size = 14),            # Gør al tekst større
    axis.title = element_text(size = 16),      # Aksetitler
    axis.text = element_text(size = 13),       # Akseværdier
    legend.text = element_text(size = 12),     # Legend
    legend.title = element_text(size = 13),
    plot.title = element_text(size = 18, face = "bold"),
    legend.position = "bottom"
  )

#################################################################################
#------------------Correlation--------------------------#
ligevægt_monthly_afkast <- ligevægt_monthly_return
ligevægt_trimmed <- ligevægt_monthly_afkast %>% filter(Date>="1963-07-01")
names(ligevægt_trimmed)[names(ligevægt_trimmed) == "Afkast"] <- "Afkast_ligevægt"

INDMOM_trimmed <- afkast_INDMOM %>% filter(Date>="1963-07-01")
names(INDMOM_trimmed)[names(INDMOM_trimmed)=="Afkast"] <- "Afkast_INDMOM"

corr_faktor_data <- FF_5_faktor %>%
 inner_join(INDMOM_trimmed, by = "Date") %>%
 inner_join(ligevægt_trimmed, by = "Date")

corr_faktor <- cor(corr_faktor_data %>% select(-Date))
View(corr_faktor)

############################################################
#Udvikling af w
###############################################################
#Plot egenværdier
plot_w_anker <- ggplot(SR_values_montly_X_120, aes(x = Date, y = Best_w)) +
  geom_line(linewidth = 1) +    
  geom_point(size = 2) +
  labs(title = "Udvikling i w - Pf2",
       x = "Tid",
       y = "W") +
  theme_minimal() +
  theme(
    axis.text = element_text(size = 16, color = "black"),
    axis.title = element_text(size = 18, face = "bold"),
    plot.title = element_text(size = 20, face = "bold", hjust = 0.5),
    panel.grid.major = element_line(color = "gray80"), 
    axis.line = element_line(linewidth = 1, colour = "black")
  )
ggsave("C:/Users/nikol/Desktopgraf.png", plot = plot_w_anker, width = 10, height = 4, dpi =300)
