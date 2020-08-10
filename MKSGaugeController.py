#    "$Name:  $";
#    "$Header: /siciliarep/CVS/tango_ds/Vacuum/VacuumController/MKSGaugeController.py,v 1.4 2007/08/28 10:39:16 srubio Exp $";
#=============================================================================
#
# file :        MKSGaugeController.py
#
# description : Python source for the MKSGaugeController and its commands. 
#                The class is derived from Device. It represents the
#                CORBA servant object which will be accessed from the
#                network. All commands which can be executed on the
#                MKSGaugeController are implemented in this file.
#
# project :    VacuumController Device Server
#
# $Author: srubio@cells.es $
#
# $Revision: 2000 $
#
# $Log: MKSGaugeController.py,v $
# Revision 1.4  2007/08/28 10:39:16  srubio
# Vacuum Controller modified to access Gauges as independent Devices
#
# Revision 1.3  2007/07/20 10:20:50  srubio
# Lot of things improved in communications and Exception management, also VarianDUAL first compatibilities added.
#
# Revision 1.2  2007/07/06 08:37:36  sicilia
# Vaig fent i provant ...
#
# Revision 1.1.1.1  2007/04/17 09:08:24  srubio
# Vacuum Controller (Gauges, Ion Pump PS, ...)
#
#
# copyleft :    Cells / Alba Synchrotron
#               Bellaterra
#               Spain
#
############################################################################
#
# This file is part of Tango-ds.
#
# Tango-ds is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Tango-ds is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, see <http://www.gnu.org/licenses/>.
##########################################################################
#

import sys,time,re
from threading import Event
import traceback

import PyTango
from PyTango import DevState,AttrQuality,DevFailed

try: import fandango
except: import PyTango_utils as fandango

from fandango.device import Dev4Tango,TimedQueue
from fandango.excepts import ExceptionWrapper,Catched,Catched2
from fandango.objects import self_locked
import fandango.functional as fun

import VacuumController
from VacuumController import getExpNumbers
from VacuumController import *

## @note Backward compatibility between PyTango3 and PyTango7
if 'PyDeviceClass' not in dir(PyTango): PyTango.PyDeviceClass = PyTango.DeviceClass
if 'PyUtil' not in dir(PyTango): PyTango.PyUtil = PyTango.Util
if 'Device_4Impl' not in dir(PyTango): PyTango.Device_4Impl = PyTango.Device_3Impl

#==================================================================
#   MKSGaugeController Class Description:
#
#         <p>This device requires <a href="http://www.tango-controls.org/Documents/tools/fandango/fandango">Fandango module<a> to be available in the PYTHONPATH.</p>
#         <p>This Device will manage the MKS 937A Gauge Controller through a SerialLine Tango Device Server.
#         It will read Pressure for each Channel, Combination Channels, Modules installed, Firmware version and relays state.</p>
#
#         <p>The right CVS command to download it is:<br>
#         cvs -d:pserver:anonymous@tango-ds.cvs.sourceforge.net:/cvsroot/tango-ds co    -r first    VacuumController</p>
#
#==================================================================
#     Device States Description:
#
#   DevState.INIT : Hardware values not readed yet (all attributes not read yeat)         
#   DevState.ON : Everything works fine
#   DevState.OFF : CCG channels switched off
#   DevState.UNKNOWN : It's not possible to communicate (errors > n_attributes)
#   DevState.ALARM : Pressure Interlock Enabled!
#   DevState.FAULT : Both cable interlock enabled!
#   DevState.DISABLE : Manual interlock enabled       
#==================================================================


#class MKSGaugeController(PyTango.Device_3Impl,Logger):
class MKSGaugeController(Dev4Tango):
    """
    <pre>
    #         This Device will manage the MKS 937A Gauge Controller through a SerialLine Tango Device Server.
    #         It will read Pressure for each Channel, Combination Channels, Modules installed, Firmware version and relays state.
    #         Last update: srubio@cells.es, 2007/09/20
    </pre>
    """

    #--------- Add you global variables here --------------------------

    #State Machine methods
    def is_Attr_allowed(self, req_type): 
        self.debug( 'In is_Attr_allowed ...')
        return bool(self.SVD and self.SVD.errors<len(self.SVD.readList) and  self.get_state() not in [PyTango.DevState.UNKNOWN] and self.SVD.init)#,PyTango.DevState.INIT] )
    is_P1_allowed=is_Attr_allowed
    is_P2_allowed=is_Attr_allowed
    is_P3_allowed=is_Attr_allowed
    is_P4_allowed=is_Attr_allowed
    is_P5_allowed=is_Attr_allowed
    is_C1_allowed=is_Attr_allowed
    is_C2_allowed=is_Attr_allowed
    is_ChannelState_allowed=is_Attr_allowed
    is_ChannelValue_allowed=is_Attr_allowed
    is_CombinationChannelState_allowed=is_Attr_allowed
    is_CombinationChannelValue_allowed=is_Attr_allowed
    is_FirmwareVersion_allowed=is_Attr_allowed
    is_ModulesInstalled_allowed=is_Attr_allowed
    is_PressureValues_allowed=is_Attr_allowed
    
    FLOAT = '[0-9](\.[0-9]{1,2})?[eE][+-][0-9]{2,2}$'
    ERROR_CODES = ['PROTECT','HV_OFF','NOGAUGE','MISCONN','LO']
    VALID_CODES = [FLOAT,'HI>','LO','AA_','WAIT','([A-Za-z]+)([ _]?)([A-Z]*)!$']+ERROR_CODES
       
    def WarmUp(self):
        funcs = {}
        funcs['CC_On(CC1)']=lambda: self.CC_On('CC1')
        funcs['CC_On(CC2)']=lambda: self.CC_On('CC2')
        funcs['CC_On(P1)']=lambda: self.CC_On('CC1')
        funcs['CC_On(P2)']=lambda: self.CC_On('CC2')
        funcs['CC_On(1)']=lambda: self.CC_On('CC1')
        funcs['CC_On(2)']=lambda: self.CC_On('CC2')
        funcs['CC_On(ALL)']=lambda: self.CC_On('ALL')
        if len(self.StartSequence)==1 and not self.StartSequence[0].startswith('#') and ',' in self.StartSequence: 
            self.StartSequence=self.StartSequence[0].split(',')
        self.StartSequence = filter(bool,(l.split('#',1)[0].strip() for l in self.StartSequence))
        if self.StartSequence:
            self.info('-'*80)
            self.info('In WarmUp() = executeStartSequence (%s)'%self.StartSequence)
            for s in self.StartSequence:
                self.info(s)
                s,c = s.split(':',1) if ':' in s else (s,'')
                try: c = True if not c else fandango.TangoEval().eval(c,_locals = self.ChannelState)
                except: c = False
                self.info('\t%s:%s'%(s,c))
                if s in funcs.keys() and callable(funcs[s]) and c:
                    self.info('In WarmUp() ... Executing %s'%s)
                    funcs[s].__call__()
                else:
                    self.info('... unknown %s'%s)
        return '\n'.join(self.StartSequence)
            
    def read_modules(self):
        self.piranis,self.modules = [],self.SVD.getComm(self.CommPrefix+'GAUGES')
        if self.modules[0:2] in ('Cv','Pr'): self.piranis.extend(['P1','P2'])
        if self.modules[2:4] in ('Cv','Pr'): self.piranis.extend(['P2','P3'])
        if self.modules[4:6] in ('Cv','Pr'): self.piranis.extend(['P4','P5'])
        #self.info('Piranis allocated in ports: %s'%self.piranis)
        return self.modules

    def read_Pressure_channel(self,attr,c_type,nchan):
        c_name=c_type+str(nchan)
        if c_type=='P':
            self.ChannelState[c_name] = 'Unknown'
        result=self.SVD.getComm(self.CommPrefix+c_type+str(nchan))
        
        self.debug(c_type+str(nchan)+' returned: '+str(result))

        #@TODO: ChannelState should be unknown only after N missreadings 
        #... do not erase last reading just because 1 error!
        
        #if self.get_state()!=DevState.ON: PyTango.Except.throw_exception('MKS_NotAllowed','Attribute reading is not allowed in this State','MKSGaugeController.read_Pressure_channel(...)')            
        if result is None or not len(result) or not any([re.match(exp,result) for exp in self.VALID_CODES]):
            if result and hasattr(self,'manageMissreadings'): 
                self.manageMissreadings(value=result)
                print 'Missreadings are '+str(self.missreadings)
            PyTango.Except.throw_exception('MKS_CommFailed','Hardware failed or not read yet','MKSGaugeController.read_Pressure_channel(...)=%s'%(result or ''))

        try:
            quality = AttrQuality.ATTR_VALID
            if 'LO' in result or 'OFF' in result:
                quality = AttrQuality.ATTR_WARNING
                attr_Px_read = 0
            elif 'PRO' in result:
                quality = AttrQuality.ATTR_ALARM
                attr_Px_read = 1
            else:
                if any([ (code in result) for code in self.ERROR_CODES]): raise Exception, 'MKS_Channel%sNotOk_%s'%(nchan,result)
                N = getExpNumbers(result)
                if N is not None:
                    attr_Px_read = float(getExpNumbers(result)[0])#float(result)
                    if '+' not in result and not 0<attr_Px_read<1:
                        if hasattr(self,'manageMissreadigns'): self.manageMissreadings(value=result)
                        else: raise Exception, 'MKS_WrongReading_%s'%result
                else: raise Exception, 'MKS_WrongReading_CHECK_%s'%result
        except Exception,e: 
            if c_type=='P':
                self.PreviousValues[nchan-1] = self.PressureValues[nchan-1]
                self.PressureValues[nchan-1] = 0.0
                self.ChannelState[c_name]=result
            print 'Exception in read_Pressure_channel: %s' %  ('MKS' in str(e) and str(e) or traceback.format_exc())
            PyTango.Except.throw_exception(str(e),'ChannelState='+str(result),'MKSGaugeController.read_Pressure_channel('+c_type+str(nchan)+')')
        
        #PressureValues is updated only when everything is OK
        if c_type=='P':
            self.PreviousValues[nchan-1] = self.PressureValues[nchan-1]
            self.PressureValues[nchan-1] = attr_Px_read
            self.ChannelState[c_name] = result #'%1.1e'%attr_Px_read#'OK'
        attr.set_value(attr_Px_read)
        attr.set_quality(quality)
        self.info('read_Pressure_channel(%s): %s,%s'%(c_name,attr_Px_read,quality))
        #attr.set_quality(PyTango.AttrQuality.VALID)
        
    def StateMachine(self,prev=None):
        """ This method manages the StateMachine of the MKSGaugeController 
        
        Changes of State are:<pre>
        #   DevState.INIT : Hardware values not readed yet (all attributes not read yeat)         
        #   DevState.ON : Everything works fine
        #   DevState.OFF : CCG channels switched off
        #   DevState.UNKNOWN : It's not possible to communicate (errors > n_attributes)
        #   DevState.ALARM : Pressure Interlock Enabled!
        #   DevState.FAULT : Both cable interlock enabled!
        #   DevState.DISABLE : Manual interlock enabled         
         </pre>
         
        A Dev4Tango.statesQueue is used; it allows to 
         
        """
        self.debug('In StateMachine() ...')
        state = prev is not None and prev or self.get_state()
        prev,channelstatus=state,''
        now = time.time()
        
        #Checking Communications status
        if not self.SerialLine or not self.SVD: #Checking if serial line is initialized
            state,channelstatus = DevState.FAULT,'SerialLine property requires a value!'
        elif not self.SVD.init: #If done in 2 lines to avoid changing to ON by default
            self.debug('State is INIT')
            state,channelstatus = DevState.INIT,'Hardware values not read yet, started at %s'%time.ctime(self.startTime)
        elif self.SVD.errors>=len(self.SVD.readList) or self.SVD.lasttime<now-2*60:
            self.debug('State is UNKNOWN or FAULT')
            state = self.SVD.errors and DevState.UNKNOWN or DevState.FAULT
            channelstatus = 'Unable to communicate since %s'%time.ctime(self.SVD.lasttime)
            for k in self.ChannelState.keys(): self.ChannelState[k]='Unknown'
        #Checking Channel state through ChannelState and ModulesInstalled
        else:
            self.debug('State is ON-relative')
            modules = self.read_modules()
            if modules.startswith('W'):
                channelstatus='WrongModuleError: %s!, check device'%modules
                self.info(channelstatus)
                state=DevState.FAULT
            else:
                ccg_states = [s.lower() for k,s in self.ChannelState.items() if k not in self.piranis]
                pir_states = [s.lower() for k,s in self.ChannelState.items() if k in self.piranis]
                #Check Protect
                if any(m in s.lower() for m in ('pro','hi') for s in self.ChannelState.values()):
                    channelstatus+='Channel readings above range!\n'
                    state=DevState.ALARM
                #If any channel is ON, state in ON/MOVING/ALARM
                elif any(re.match(reg,s) for reg in ('ok',self.FLOAT,'lo') for s in ccg_states):
                    state=DevState.ON
                    #Check Default Status (or just first channel if not defined)
                    if any(re.match('lo',s) for s in ccg_states):
                            channelstatus+='Channel readings below range!: %s\n'%str(ccg_states)
                            state=DevState.MOVING
                    for i,s in enumerate(self.DefaultStatus.split(',') or ['']):
                        if s.lower().strip()=='on' and 'off' in self.ChannelState.values()[i].lower():
                            channelstatus+='Channel %d should be ON!\n'%i
                            state=DevState.ALARM
                    if state in (DevState.ON,DevState.MOVING):
                        #Check Piranis
                        if  any(re.match(self.FLOAT,s) for s in pir_states):
                            if any(re.match(self.FLOAT,s) for s in ccg_states):
                                state=DevState.MOVING #Both Pirani and CCG have readings
                            else:
                                state=DevState.ALARM #CCG out of range, reading Pirani
                            channelstatus+="Pirani has readings!\n"
                        else:
                            channelstatus+='Controller is working properly.\n'
                        #Check oscillation
                        for old,new in zip(self.PreviousValues,self.PressureValues):
                            if old and new and not (.5<(old/new)<1.5): 
                                state=DevState.MOVING                
                                channelstatus+="Gauge oscillates between %s and %s!\n" % (old,new)
                                break
                #If everything is OFF
                elif all('off' in s for s in ccg_states):
                    channelstatus+='HV output is Off.\n'
                    state=DevState.OFF
                #If there are other error messages
                else:
                    channelstatus+='Some Controller Channel is NOT working properly, check device.\n'
                    self.info('Controller %s: %s'%(str(state),'; '.join(self.ChannelState.values())))
                    #<-State MUST be ALARM, to avoid CCG showing fake attribute readings!
                    state=DevState.ALARM if any(fandango.matchAny(self.VALID_CODES,s) for s in ccg_states) else DevState.FAULT
                #channelstatus+='Channels:\n'
                channelstatus+=','.join(['OK' in s and str(self.PressureValues[fun.str2int(k)-1]) or s for k,s in sorted(self.ChannelState.items()) if re.match('P[0-9]',k)])+'\n'
        self.channelstatus = channelstatus
        return state

#------------------------------------------------------------------
#    Device constructor
#------------------------------------------------------------------
    def __init__(self,cl, name):
        #PyTango.Device_3Impl.__init__(self,cl,name)
        Dev4Tango.__init__(self,cl,name)
        MKSGaugeController.init_device(self)

#------------------------------------------------------------------
#    Device destructor
#------------------------------------------------------------------
    def delete_device(self):
        self.warning( "[Device delete_device method] for device %s"%self.get_name())
        if self.SVD: self.SVD.stop()
        #del self.SVD
        
    def __del__(self):
        if self.SVD: self.SVD.stop()
        try:type(self).__base__.__del__(self)
        except:pass


#------------------------------------------------------------------
#    Device initialization
#------------------------------------------------------------------
    def init_device(self):
        print "In ", self.get_name(), "::init_device()"
        self.exception,self.init_error,self.comms_report,self.channelstatus='','','',''
        self.last_state_change=0
        try:
            self.init_my_Logger()            
            self.get_device_properties(self.get_device_class())
            if not hasattr(self,'LogLevel'): self.LogLevel = 'DEBUG'
            self.setLogLevel(self.LogLevel)            
            self.info(''.join(("In ", self.get_name(), "::init_device(%s)"%self.LogLevel)))
            self.set_state(PyTango.DevState.UNKNOWN)
                        
            self.startTime = time.time()
            self.statesQueue = TimedQueue(self.get_state())
            
            if not hasattr(self,'Refresh') or not self.Refresh:
                self.warning('Refresh attribute does not exists!')
                self.Refresh=0.5
            elif self.Refresh>5.:
                self.info('Refresh period is limited to 5. seconds.')
                self.Refresh = 5.
            self.info('Refresh period for full attribute reading cycle set to %s seconds.'%self.Refresh)
        
            self.ChannelState={}#['Unknown']*5
            self.PreviousValues=[0.0]*5
            self.PressureValues=[0.0]*5
            
            try:
                self.CommPrefix = ('422' in self.Protocol or '485' in self.Protocol) and '$0' or '' 
            except: #Protocol property has not been set
                self.CommPrefix = '' 
                
            # Setting the Exception Wrapping and tracing 
            self.last_exception=(time.time(),'')
            def postException(exstring):
                self.last_exception=(time.time(),exstring)
                #self.last_exception_epoch=time.time()
                pass
            
            if self.LogLevel=='DEBUG':
                self.read_Pressure_channel=ExceptionWrapper(self.read_Pressure_channel,
                    logger=self,
                    verbose=True,
                    postmethod=(lambda exstring: self.__setattr__('last_exception',(time.time(),exstring)))
                    )
                
            if not self.SerialLine:
                self.SVD = None
                self.set_state(PyTango.DevState.FAULT)
                self.error('SerialLine property requires a value!')
                self.set_status('SerialLine property requires a value!')
                #raise RuntimeError, str('SerialLine property requires a value!')
            else:
                #The arguments for SerialVacuumDevice are:
                #    tangoDevice=SerialLineName, period=minimum time between communications, wait=time waiting for answer
                from VacuumController import SerialVacuumDevice
                self.SVD=SerialVacuumDevice(
                    tangoDevice=self.SerialLine,
                    period=self.Refresh, #Total refresh period divided by number of commands
                    wait=0.01, #Maximum time waiting for each command to succeed.
                    retries=3,
                    log=self.LogLevel)
                    
                r = 60. #self.Refresh*5
                self.SVD.setPolledComm(self.CommPrefix+'P1',r)
                self.SVD.setPolledComm(self.CommPrefix+'P2',self.Refresh)
                self.SVD.setPolledComm(self.CommPrefix+'P3',r)
                self.SVD.setPolledComm(self.CommPrefix+'P4',r)
                self.SVD.setPolledComm(self.CommPrefix+'P5',r)

                r = 60. #self.Refresh*5
                self.SVD.setPolledComm(self.CommPrefix+'C1',r) #,slow)
                self.SVD.setPolledComm(self.CommPrefix+'C2',r)
                [self.SVD.setPolledComm(self.CommPrefix+'PRO%d'%i,r) for i in (1,2)]
                [self.SVD.setPolledComm(self.CommPrefix+'RLY%d'%i,r) for i in range(1,6)]
                self.SVD.setPolledComm(self.CommPrefix+'RELAYS',r)
                
                r = 60.
                self.SVD.setPolledComm(self.CommPrefix+'GAUGES',r)
                self.SVD.setPolledComm(self.CommPrefix+'VER',r)
                self.SVD.start()
            
        except Exception,e:
            self.error('Exception in MKSGaugeController.init_device(): '+traceback.format_exc())
            self.init_error='Exception in MKSGaugeController.init_device(): '+str(e)
            PyTango.Except.throw_exception("MKSGaugeController_initDeviceException",str(e),str(e))            
        
        #self.last_state = self.get_state()
        self.info("Ready to accept request.")
        self.info('-'*80)

#------------------------------------------------------------------
#    Always excuted hook method
#------------------------------------------------------------------
    def always_executed_hook(self):
        self.debug("In "+self.get_name()+"::always_executed_hook()")
        try:
            prev = self.get_state()
            try: self.read_ChannelState() #Updating ChannelState from cached serial values
            except: pass
            state = self.StateMachine(prev)
            
            if self.SerialLine and self.SVD:
                self.comms_report=self.SVD.getReport()
                status = '\n'.join(s for s in [self.channelstatus,self.Description,self.init_error,self.comms_report,'',self.exception.replace('\n',''),] if s)
            else: 
                self.debug('SerialLine property requires a value!')
                status = 'SerialLine property requires a value!'            
            
            if prev!=state: #New states are added to StatesQueue
                keep_time = 20 #Any Wrong State should be kept at least for 20 seconds!
                if self.statesQueue.index(state) is None:   
                    self.statesQueue.append(state,1 if state==DevState.ON else keep_time)
            
            #Getting next state to process (it will be actual state if there's no new states in queue)
            st = self.statesQueue.pop()
            if st!=state or state!=prev: 
                self.info('State = %s,  StateMachine returned %s (previous was %s)'%(st,state,prev))
                self.info(self.channelstatus)
            state = st

            if prev!=state:
                self.info( '*'*80)
                self.info('%s.State changed from %s to %s'%(self.get_name(),str(prev),str(state)))
                self.info(status)
                self.info( '*'*80)
                self.last_state_change=time.time()
                self.set_state(state)
                #self.last_state = state                
                if prev==DevState.INIT and state!=DevState.UNKNOWN:
                    if self.StartSequence: 
                        self.WarmUp()
    
            self.set_status(status[:200])
        
        except Exception,e:
            self.error('Exception in always_executed_hook: %s'%str(e))
            print traceback.format_exc()

#==================================================================
#
#    MKSGaugeController read/write attribute methods
#
#==================================================================
#------------------------------------------------------------------
#    Read Attribute Hardware
#------------------------------------------------------------------
    def read_attr_hardware(self,data):
        self.debug("In "+self.get_name()+"::read_attr_hardware()")


#------------------------------------------------------------------
#    Read P1 attribute
#------------------------------------------------------------------
    @self_locked
    def read_P1(self, attr):
        self.debug("In "+self.get_name()+"::read_P1()")
        
        #    Add your own code here
        self.read_Pressure_channel(attr,'P',1)


#------------------------------------------------------------------
#    Read P2 attribute
#------------------------------------------------------------------
    @self_locked
    def read_P2(self, attr):
        self.debug("In "+self.get_name()+"::read_P2()")
        
        #    Add your own code here
        self.read_Pressure_channel(attr,'P',2)


#------------------------------------------------------------------
#    Read P3 attribute
#------------------------------------------------------------------
    @self_locked
    def read_P3(self, attr):
        self.debug("In "+self.get_name()+"::read_P3()")
        
        #    Add your own code here
        self.read_Pressure_channel(attr,'P',3)


#------------------------------------------------------------------
#    Read P4 attribute
#------------------------------------------------------------------
    @self_locked
    def read_P4(self, attr):
        self.debug("In "+self.get_name()+"::read_P4()")
        
        #    Add your own code here
        self.read_Pressure_channel(attr,'P',4)


#------------------------------------------------------------------
#    Read P5 attribute
#------------------------------------------------------------------
    @self_locked
    def read_P5(self, attr):
        self.debug("In "+self.get_name()+"::read_P5()")
        
        #    Add your own code here
        self.read_Pressure_channel(attr,'P',5)

##------------------------------------------------------------------
##    Read C1 attribute
##------------------------------------------------------------------
    #def read_C1(self, attr):
        #self.debug("In "+self.get_name()+"::read_C1()")
        
        ##    Add your own code here
        #self.read_Pressure_channel(attr,'C',1)

##------------------------------------------------------------------
##    Read C2 attribute
##------------------------------------------------------------------
    #def read_C2(self, attr):
        #self.debug("In "+self.get_name()+"::read_C2()")
        
        ##    Add your own code here
        #self.read_Pressure_channel(attr,'C',2)

#------------------------------------------------------------------
#    Read ChannelState attribute
#------------------------------------------------------------------
    @self_locked
    def read_ChannelState(self, attr=None):
        self.debug("In "+self.get_name()+"::read_ChannelState()")
        
        #    Add your own code here
        for i in range(5):
            s = self.SVD.getComm(self.CommPrefix+'P'+str(i+1))
            try:
                float(s)
                s=s#'OK'
            except: pass
            self.ChannelState['P'+str(i+1)] = s or 'Unknown'
        attr_ChannelState_read=[]
        for k,v in sorted(self.ChannelState.items()):
            attr_ChannelState_read.append('%s:%s'%(k,v))
        if attr is not None:
            attr.set_value(attr_ChannelState_read)


##------------------------------------------------------------------
##    Read ChannelValue attribute
##------------------------------------------------------------------
    #def read_ChannelValue(self, attr):
        #self.debug("In "+self.get_name()+"::read_ChannelValue()")
        
        ##    Add your own code here
        
        #attr_ChannelValue_read = 1.0
        #attr.set_value(attr_ChannelValue_read)


##------------------------------------------------------------------
##    Read CombChannelState attribute
##------------------------------------------------------------------
    #def read_CombChannelState(self, attr):
        #self.debug("In "+self.get_name()+"::read_CombChannelState()")
        
        ##    Add your own code here
        
        #attr_CombChannelState_read = "Attribute not implemented yet"
        #attr.set_value(attr_CombChannelState_read)


##------------------------------------------------------------------
##    Read CombChannelValue attribute
##------------------------------------------------------------------
    #def read_CombChannelValue(self, attr):
        #self.debug("In "+self.get_name()+"::read_CombChannelValue()")
        
        ##    Add your own code here
        
        #attr_CombChannelValue_read = 0.0
        #attr.set_value(attr_CombChannelValue_read)


#------------------------------------------------------------------
#    Read FirmwareVersion attribute
#------------------------------------------------------------------
    def read_FirmwareVersion(self, attr):
        self.debug("In "+self.get_name()+"::read_FirmwareVersion()")
        
        #    Add your own code here
        try:                    
            attr_FirmwareVersion_read = self.SVD.getComm(self.CommPrefix+'VER')
            attr.set_value(attr_FirmwareVersion_read)
        except DevFailed, e:
            PyTango.Except.re_throw_exception(e,"DevFailed Exception",traceback.format_exc())
            
            
#------------------------------------------------------------------
#    Read SerialLine attribute
#------------------------------------------------------------------
    def read_SerialLine(self, attr):
        self.debug("In "+self.get_name()+"::read_SerialLine()")
        
        #    Add your own code here
        attr_SerialLine_read = self.SerialLine[:]
        attr.set_value(attr_SerialLine_read)                    


#------------------------------------------------------------------
#    Read ModulesInstalled attribute
#------------------------------------------------------------------
    def read_ModulesInstalled(self, attr=None):
        self.debug("In "+self.get_name()+"::read_ModulesInstalled()")
        
        #    Add your own code here
        try:                    
            modules = self.read_modules()
            CC,A,B=modules[0:2],modules[2:4],modules[4:]
            codes={
                'Hc':'HotCathode',
                'Cc':'ColdCathode',
                'Pr':'Pirani',
                'Cv':'ConvectionPirani',
                'Tc':'DualThermocouple',
                'Cm':'DualManometer',
                'P1':'SinglePirani',
                'C1':'SingleConvectionPirani',
                'T1':'SingleThermocouple',
                'M1':'SingleManometer',
                'Nc':'NoModule',
                'Wc':'WrongModuleConnected',
                }
            attr_ModulesInstalled_read = 'P1=CC:%s; P2=A:%s; P4=B:%s'%(codes[CC],codes[A],codes[B])
            if attr:
                attr.set_value(attr_ModulesInstalled_read)
            else:
                return attr_ModulesInstalled_read
        except DevFailed, e:
            PyTango.Except.re_throw_exception(e,"DevFailed Exception",traceback.format_exc())


#------------------------------------------------------------------
#    Read PressureValues attribute
#------------------------------------------------------------------
    def read_PressureValues(self, attr):
        self.debug("In "+self.get_name()+"::read_PressureValues()")
        
        #    Add your own code here
        for i,k in enumerate(sorted(self.ChannelState.keys())):
            try:
                s = self.SVD.getComm(self.CommPrefix+k)
                v = float(s)
            except:
                v = 0.0
            self.PreviousValues[i] = self.PressureValues[i]
            self.PressureValues[i] = v
        
        attr_PressureValues_read = self.PressureValues #[1.0]
        attr.set_value(attr_PressureValues_read, 5)
        
#------------------------------------------------------------------
#    Read ProtectSetPoints attribute
#------------------------------------------------------------------
    def read_ProtectSetpoints(self, attr):
        self.debug( "In "+ self.get_name()+ "::read_ProtectSetpoints()")
        
        #    Add your own code here
        attr_read = [s for s in (self.SVD.getComm(self.CommPrefix+'PRO%d'%i) for i in (1,2))]
        attr.set_value(attr_read, len(attr_read))
        
#------------------------------------------------------------------
#    Write ProtectSetPoints attribute
#------------------------------------------------------------------
    def write_ProtectSetpoints(self, attr):
        self.debug( "In "+ self.get_name()+ "::write_ProtectSetpoints()")
        data=[]
        attr.get_write_value(data)

        #    Add your own code here
        if len(data)!=2:
            PyTango.Except.throw_exception('WrongDataLenght','%s: Data length should be equal to 2 (%d)'%(data,len(data)),
                'write_ProtectSetpoints')
        data = map(float,data)
        comms = [self.CommPrefix+('PRO%d=%1.1e'%(i+1,d)).upper() for i,d in enumerate(data)]
        self.SendCommand(comms)
        
#   RelaySetpoints

#------------------------------------------------------------------
#    Read RelaySetpoints attribute
#------------------------------------------------------------------
    def read_RelaySetpoints(self, attr):
        self.debug( "In "+ self.get_name()+ "::read_RelaySetpoints()")
        
        #    Add your own code here
        attr_read = [s for s in (self.SVD.getComm(self.CommPrefix+'RLY%d'%i) for i in (1,2,3,4,5))]
        attr.set_value(attr_read, len(attr_read))
        
#------------------------------------------------------------------
#    Write ProtectSetpoints attribute
#------------------------------------------------------------------
    def write_RelaySetpoints(self, attr):
        self.debug( "In "+ self.get_name()+ "::write_RelaySetpoints()")
        data=[]
        attr.get_write_value(data)

        #    Add your own code here
        if len(data)!=5:
            PyTango.Except.throw_exception('WrongDataLenght','Data length should be equal to 5',
                'write_RelaySetPoints')
        data = map(float,data)
        self.SendCommand([self.CommPrefix+('RLY%d=%1.1e'%(i+1,d)).upper() for i,d in enumerate(data)])

#   Relays

#------------------------------------------------------------------
#    Read Relays attribute
#------------------------------------------------------------------
    def read_Relays(self, attr):
        self.debug( "In "+ self.get_name()+ "::read_Relays()")
        
        #    Add your own code here
        attr_read = [bool(int(s)) for s in self.SVD.getComm(self.CommPrefix+'RELAYS').strip()[-5:]]
        attr.set_value(attr_read, len(attr_read))

#==================================================================
#
#    MKSGaugeController command methods
#
#==================================================================

#------------------------------------------------------------------
#    SendCommand command:
#
#    Description: Sends a command directly to the device through the rs232 line
#                
#    argin:  DevString    Command to send (literally)
#    argout: DevString    Answer received (literally)
#------------------------------------------------------------------
    def SendCommand(self, argin,separator='\n'):
        self.debug("In "+self.get_name()+"::SendCommand()")
        #    Add your own code here
        self.info('>'*80)
        result = ''
        self.SVD.stop()
        if self.SVD.Alive:
            self.warning( 'SVD IS STILL ALIVE!!!')
        try:
            argin = fun.toSequence(argin)
            for arg in argin:
                result+=self.SVD.serialComm(arg)+separator
                self.info('===> %s'%(arg))
                self.SVD.event.wait(.1)
            result = result.strip()
            self.info('<=== %s'%result)
        except PyTango.DevFailed, e:
            self.error( 'Exception in sendCommand():'+ str(e))
            raise Exception('Exception in sendCommand():', str(e))
        except Exception,e:
            self.error('Exception in sendCommand():%s'%traceback.format_exc())
            #self.setStatus(self.getStatus())
            raise Exception('Exception in sendCommand():', traceback.format_exc())
        self.SVD.start()
        self.info('<'*80)
        return result
    
#------------------------------------------------------------------
#    getChannelState command:
#
#    Description: Gets the state for a channel
#                
#    argin:  DevString    Channel name
#    argout: DevString    Channel state
#------------------------------------------------------------------
    def getChannelState(self, argin):
        self.debug("In "+self.get_name()+"::getChannelState()")
        #    Add your own code here
        if argin in self.ChannelState.keys():
            argout=self.ChannelState[argin]
        else:
            argout='UNKNOWN'
        return argout
        
#------------------------------------------------------------------
#    On command:
#
#    Description:  Switchs On HighVoltage for CCs configured as on in DefaultStatus property
#                
#    argout: DevString     Switchs On HighVoltage for CCs configured as on in DefaultStatus property
#------------------------------------------------------------------
    def On(self):
        self.warning("In "+self.get_name()+"::On()")
        #    Add your own code here
        if not self.DefaultStatus:
            modules = self.read_modules()
            if modules[2:4]=='Cc': status = 'On,On'
            else: status = 'On'
        else: status = self.DefaultStatus
        
        replies = []
        for i,s in enumerate(status.split(',')):
            if s.lower().strip()=='on':
                replies.append(str(self.CC_On('P%d'%(i+1))))
        return ','.join(replies)
            
#------------------------------------------------------------------
#    Off command:
#
#    Description:  Switchs Off both HighVoltages
#                
#    argout: DevString     Switchs Off both HighVoltages
#------------------------------------------------------------------
    def Off(self):
        self.warning("In "+self.get_name()+"::Off()")
        #    Add your own code here
        return self.CC_Off('ALL')
        
#------------------------------------------------------------------
#    CC_On command:
#
#    Description: Gets the state for a channel
#                
#    argin:  DevString    Channel name
#    argout: DevString    Switchs On HighVoltage for a CC, arg should be ALL, CC1, CC2, P1 or P2
#------------------------------------------------------------------
    @self_locked
    def CC_On(self, argin):
        argin=argin.upper().strip()        
        self.warning("In "+self.get_name()+"::CC_On(%s)"%argin)
        #    Add your own code here
        chans={'CC1':1,'C1':1,'CCG1':1,'P1':1,'CC2':2,'C2':2,'CCG2':2,'P2':2,'CC3':4,'P4':4,'P5':5,
                    '1':1,'2':2,'3':3,'4':4,'5':5}
        if argin=='ALL':
            result = [self.CC_On('P1')]
            modules = self.read_modules()
            if modules[2:4]=='Cc': result.append(self.CC_On('P2'))
            if modules[4:]=='Cc': result.append(self.CC_On('P4'))
            return ','.join(result)
        elif argin in chans.keys():
            ev = Event()
            command=self.CommPrefix+'ECC'+str(chans[argin])
            result=self.SendCommand(command)
            if 'AGAIN' in result:
                result=self.SendCommand(command)
            if 'PENDING' in result:
                ev.wait(0.51)
                result=self.SendCommand(command)
            return result
        else:
            raise Exception('CC_On_UnknownChannel%s'%str(argin))

#------------------------------------------------------------------
#    CC_Off command:
#
#    Description: Gets the state for a channel
#                
#    argin:  DevString    Channel name
#    argout: DevString    Channel state
#------------------------------------------------------------------
    @self_locked
    def CC_Off(self, argin):
        argin=argin.upper().strip()        
        self.warning("In "+self.get_name()+"::CC_Off(%s)"%argin)
        #    Add your own code here
        chans={'CC1':1,'C1':1,'CCG1':1,'P1':1,'CC2':2,'C2':2,'CCG2':2,'P2':2,'CC3':4,'P4':4,'P5':5,
                    '1':1,'2':2,'3':3,'4':4,'5':5}
        if argin=='ALL':
            result = [self.CC_Off('P1')]
            modules = self.read_modules()
            if modules[2:4]=='Cc': result.append(self.CC_Off('P2'))
            if modules[4:]=='Cc': result.append(self.CC_Off('P4'))
            return ','.join(result)
        elif argin in chans.keys():
            command=self.CommPrefix+'XCC'+str(chans[argin])
            result=self.SendCommand(command)
            return result
        else:
            raise Exception('CC_Off_UnknownChannel%s'%str(argin))


#==================================================================
#
#    MKSGaugeControllerClass class definition
#
#================================================================== 
class MKSGaugeControllerClass(PyTango.PyDeviceClass):

    #    Class Properties
    class_property_list = {
        'Refresh':
            [PyTango.DevDouble,
            "Period (in seconds) for the internal refresh thread.",
            [ 3. ] ],
        }


    #    Device Properties
    device_property_list = {
        'SerialLine':
            [PyTango.DevString,
            "SerialLine Device Server to connect with",
            [''] ],
        'Protocol':
            [PyTango.DevString,
            "SerialLine Physical Protocol used (232/422/485)",
            ['232'] ],            
        'NChannels':
            [PyTango.DevLong,
            "Number of Pressure Channels available",
            [ 5 ] ],
        'NCombChannels':
            [PyTango.DevLong,
            "Number of Combination Channels available",
            [ 2 ] ],
        'Description':
            [PyTango.DevString,
            "This string field will appear in the status and can be used to add extra information about equipment location",
            [''] ],
        'Refresh':
            [PyTango.DevDouble,
            "Period (in seconds) for the internal refresh thread (1 entire cycle).",
            [ 0.1 ] ],
        'DefaultStatus':
            [PyTango.DevString,
            "On/Off,On/Off; the expected status for each channel, empty if not used",
            [''] ],
        'LogLevel':
            [PyTango.DevString,
            "This property selects the log level (DEBUG/INFO/WARNING/ERROR)",
            ['INFO'] ],
        'StartSequence':
            [PyTango.DevVarStringArray,
            "Commands available are: CC_On(1),CC_On(2); Conditions like CC_On(1):bl/vc/pir/p < 1e-4 can be used to have control over warmup.",
            ['#CC_On(CC1):"OFF" in P1 and "LO" in P4 #or CC_On(CC2) or CC_On(ALL)'] ],
        }


    #    Command definitions
    cmd_list = {
        'SendCommand':
            [[PyTango.DevString, "Command to send (literally)"],
            [PyTango.DevString, "Sends Serial Command and returns the answer received (literally)"],
            {
                'Display level':PyTango.DispLevel.EXPERT,
             } ],
        'getChannelState':
            [[PyTango.DevString, "Channel name"],
            [PyTango.DevString, "Get State for Channel"]],
        'On':
            [[PyTango.DevVoid, "Switchs On HighVoltage for CCs configured as on in DefaultStatus property"],
            [PyTango.DevString, "Switchs On HighVoltage for CCs configured as on in DefaultStatus property"],
            {
                'Display level':PyTango.DispLevel.EXPERT,
             } ],
        'Off':
            [[PyTango.DevVoid, "Switchs On HighVoltage for CCs configured as on in DefaultStatus property"],
            [PyTango.DevString, "Switchs On HighVoltage for CCs configured as on in DefaultStatus property"],
            {
                'Display level':PyTango.DispLevel.EXPERT,
             } ],             
        'CC_On':
            [[PyTango.DevString, "Switchs On HighVoltage for a CC, arg should be ALL, CC1, CC2, P1 or P2"],
            [PyTango.DevString, "Switchs On HighVoltage for a CC,, arg should be ALL, CC1, CC2, P1 or P2"],
            {
                'Display level':PyTango.DispLevel.EXPERT,
             } ],
        'CC_Off':
            [[PyTango.DevString, "Switchs Off HighVoltage for a CC, arg should be ALL, CC1, CC2, P1 or P2"],
            [PyTango.DevString, "Switchs Off HighVoltage for a CC,, arg should be ALL, CC1, CC2, P1 or P2"],
            {
                'Display level':PyTango.DispLevel.EXPERT,
             } ],
        'WarmUp':
            [[PyTango.DevVoid, "Executes StartSequence"],
            [PyTango.DevString, "Executes StartSequence"],
            {'Display level':PyTango.DispLevel.EXPERT,} ],
        }


    #    Attribute definitions
    attr_list = {
        'P1':
            [[PyTango.DevDouble,
            PyTango.SCALAR,
            PyTango.READ],
            {
                'unit':"mbar",
                'format':"%5.2e",
            } ],
        'P2':
            [[PyTango.DevDouble,
            PyTango.SCALAR,
            PyTango.READ],
            {
                'unit':"mbar",
                'format':"%5.2e",
            } ],
        'P3':
            [[PyTango.DevDouble,
            PyTango.SCALAR,
            PyTango.READ],
            {
                'unit':"mbar",
                'format':"%5.2e",
            } ],
        'P4':
            [[PyTango.DevDouble,
            PyTango.SCALAR,
            PyTango.READ],
            {
                'unit':"mbar",
                'format':"%5.2e",
            } ],
        'P5':
            [[PyTango.DevDouble,
            PyTango.SCALAR,
            PyTango.READ],
            {
                'unit':"mbar",
                'format':"%5.2e",
            } ],
        #"""'C1':
            #[[PyTango.DevDouble,
            #PyTango.SCALAR,
            #PyTango.READ],
            #{
                #'unit':"mbar",
                #'format':"%5.2e",
            #} ],
        #'C2':
            #[[PyTango.DevDouble,
            #PyTango.SCALAR,
            #PyTango.READ],
            #{
                #'unit':"mbar",
                #'format':"%5.2e",
            #} ],"""
        'ChannelState':
            [[PyTango.DevString,
            PyTango.SPECTRUM,
            PyTango.READ, 7]],
        #"""'ChannelValue':
            #[[PyTango.DevDouble,
            #PyTango.SCALAR,
            #PyTango.READ],
            #{
                #'label':"Pressure Channel",
                #'unit':"mbar",
            #} ],"""
        #"""'CombChannelState':
            #[[PyTango.DevString,
            #PyTango.SCALAR,
            #PyTango.READ]],
        #'CombChannelValue':
            #[[PyTango.DevDouble,
            #PyTango.SCALAR,
            #PyTango.READ],
            #{
                #'label':"Combination Channel",
                #'unit':"mbar",
            #} ],"""
        'FirmwareVersion':
            [[PyTango.DevString,
            PyTango.SCALAR,
            PyTango.READ]],
        'SerialLine':
            [[PyTango.DevString,
            PyTango.SCALAR,
            PyTango.READ]],            
        'ModulesInstalled':
            [[PyTango.DevString,
            PyTango.SCALAR,
            PyTango.READ]],
        'PressureValues':
            [[PyTango.DevDouble,
            PyTango.SPECTRUM,
            PyTango.READ, 256],
            {
                'unit':"mbar",
                #'format':"scientific;uppercase;setprecision(3)",
            } ],
        'ProtectSetpoints':
            [[PyTango.DevString,
            PyTango.SPECTRUM,
            PyTango.READ_WRITE, 5]],
        'RelaySetpoints':
            [[PyTango.DevString,
            PyTango.SPECTRUM,
            PyTango.READ_WRITE, 5]],
        'Relays':
            [[PyTango.DevBoolean,
            PyTango.SPECTRUM,
            PyTango.READ, 5]],
        'Missreadings':
            [[PyTango.DevString,
            PyTango.SPECTRUM,PyTango.READ, 256],
            {'Display Level':PyTango.DispLevel.EXPERT,}, 
            ],
        }



#------------------------------------------------------------------
#    MKSGaugeControllerClass Constructor
#------------------------------------------------------------------
    def __init__(self, name):
        PyTango.PyDeviceClass.__init__(self, name)
        self.set_type(name);
        print "In MKSGaugeControllerClass  constructor"
        
def addLoggingToTangoClass(Klass):
    #Dev must inherit from Dev4Tango
    #Dev.init_device=#USE A DECORATOR HERE!!!
    Klass.device_property_list['LogLevel']=\
            [PyTango.DevString,
            "LogLevel: ERROR/WARNING/INFO/DEBUG",
            ['INFO'] ]
    return Klass
#MKSGaugeControllerClass.device_property_list['LogLevel']=[PyTango.DevString,"LogLevel: ERROR/WARNING/INFO/DEBUG",['INFO'] ]
MKSGaugeControllerClass=addLoggingToTangoClass(MKSGaugeControllerClass)
    
def manageMissreadings(obj,attr=None,value=None):
    if not hasattr(obj,'missreadings'): setattr(obj,'missreadings',[])
    if value is not None and value not in obj.missreadings: obj.missreadings.append(str(value))
    if len(obj.missreadings)>256: obj.missreadings=obj.missreadings[-256:-1]+[obj.missreadings[-1]]
    if attr is not None: attr.set_value(obj.missreadings)
    return obj.missreadings
    
MKSGaugeController.manageMissreadings = manageMissreadings
MKSGaugeController.read_Missreadings = manageMissreadings

#==================================================================
#
#    MKSGaugeController class main method
#
#==================================================================
def main():
    try:
        py = PyTango.PyUtil(sys.argv)
        py.add_TgClass(MKSGaugeControllerClass,MKSGaugeController,'MKSGaugeController')

        U = PyTango.Util.instance()
        U.server_init()
        U.server_run()

    except PyTango.DevFailed,e:
        print '-------> Received a DevFailed exception:',traceback.format_exc()
    except Exception,e:
        print '-------> An unforeseen exception occured....',traceback.format_exc()
        
if __name__ == '__main__':
    main()
